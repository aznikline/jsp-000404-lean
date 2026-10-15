import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h13, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h10, h18, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h13, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h13, h22, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h10, h13, h24, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h11, h26, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h2, h21, h26, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                · linarith only [h0, h10, h13, h21, h29, h4, h7, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h10, h13, h21, h31, h4, h7, h9, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h10, h13, h21, h33, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h0, h10, h13, h21, h35, h4, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h13, h35, h4, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
        · linarith only [h0, h10, h4, h40, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
          · linarith only [h0, h10, h4, h42, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
            · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
              · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h1, h44, h49, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h2, h45, h49, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h40, h45, h48, hlam]
                  · linarith only [h0, h4, h40, h45, h46, h47, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h0, h10, h4, h46, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h4, h45, h55, h57, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h40, h57, h7, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h10, h4, h56, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h10, h44, h55, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h4, h44, h63, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h4, h63, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h10, h4, h44, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h4, h66, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
      · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
        · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
          · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
            · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
              · linarith only [h2, h73, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                · linarith only [h0, h69, h75, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h72, h75, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
              · linarith only [h2, h78, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                · linarith only [h0, h69, h80, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h4, h69, h7, h72, h82, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h5, h84, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h7, h86, h9, hlam]
                      · rcases h0bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h69, h72, h8, h86, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h69, h7, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h69, h7, h72, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h0, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h69, h72, h8, h86, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo1]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h0, h69, h7, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h0, h69, h7, h72, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h1, hlam, p88_1]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h4, hlam, p88_1]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h69, h7, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo2]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h0, h4, h69, h7, h72, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h2, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h5, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h7, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h9, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h3, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h6, hlam, p88_1]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h8, hlam, p88_0]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [h69, h7, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1, u0elo4]
                        · have p88_0 := h88c.1
                          have p88_1 := h88c.2.1
                          have p88_2 := h88c.2.2.1
                          have p88_3 := h88c.2.2.2
                          linarith only [hlam, p88_0]
          · linarith only [h0, h6, h69, h71, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h0, h5, h69, h70, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
        · linarith only [h0, h116, h4, h69, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
          · linarith only [h0, h118, h4, h69, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
              · linarith only [h121, h2, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                    · linarith only [h0, h118, h125, h5, h6, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                      · linarith only [h1, h120, h127, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases h0bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h4, h69, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h124, h4, hc35, hlam, hphi, ht0b, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h116, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h116, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h0, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h4, h69, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h0, h116, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h0, h116, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h1, hlam, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h4, hlam, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h116, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo2]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h0, h116, h4, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h2, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h5, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h7, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h9, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h3, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h6, hlam, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h8, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h116, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo4]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                  · linarith only [h0, h116, h123, h124, h4, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h120, h123, h69, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
              · linarith only [h157, h2, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                · linarith only [h120, h159, h4, h69, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h159, h69, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
    · linarith only [h162, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
      · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
        · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
          · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
            · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
              · linarith only [h162, h168, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                · linarith only [h0, h164, h170, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h167, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h167, h7, h8, hc13, hc35, hlam, hphi]
          · linarith only [h0, h164, h166, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h0, h164, h165, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
        · linarith only [h0, h164, h176, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
          · linarith only [h0, h164, h178, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
            · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
              · linarith only [h162, h181, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                  · linarith only [h0, h184, h4, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                    · linarith only [h162, h186, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                      · linarith only [h162, h176, h180, h188, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h0bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h164, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p190_1, u0elo0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h176, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h176, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h176, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h0, hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h176, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo1]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h0, h176, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h0, h176, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h1, hlam, p190_1]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h4, hlam, p190_1]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h176, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo2]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h8, hlam, p190_1]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h2, hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h5, hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h7, hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h162, hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h3, hlam, p190_0]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h6, hlam, p190_1]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h1, h180, hc34, hlam, hphi, ht0b, ht45, ht5b, p190_1, u0elo4]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [h176, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p190_1, u0elo4]
                        · have p190_0 := h190c.1
                          have p190_1 := h190c.2.1
                          have p190_2 := h190c.2.2.1
                          have p190_3 := h190c.2.2.2
                          linarith only [hlam, p190_0]
                · linarith only [h1, h164, h180, h183, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h180, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h218 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
  · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
    · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
      · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
        · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
          · linarith only [h1, h223, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
            · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
              · linarith only [h218, h220, h226, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                · linarith only [h0, h221, h226, h228, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h218, h228, h7, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
              · linarith only [h0, h231, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                · linarith only [h0, h219, h220, h223, h225, h233, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h218, h233, h7, hc23, hc34, hlam, hphi]
        · linarith only [h0, h220, h222, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h220, h221, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
      · linarith only [h0, h220, h238, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
        · linarith only [h0, h220, h240, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
          · linarith only [h1, h242, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
            · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
              · linarith only [h245, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
                · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                    · rcases h0bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h247, h4, hc35, hlam, hphi, ht0b, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h2, h244, hc45, hlam, hphi, ht0b, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h240, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h0, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h247, h4, hc35, hlam, hphi, ht0b, ht5b, p250_1, u0elo1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h0, h2, h244, hc45, hlam, hphi, ht0b, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h0, h240, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h1, hlam, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h4, hlam, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h7, hlam, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h240, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p250_1, u0elo2]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h2, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h5, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h2, h247, h4, hc35, hlam, hphi, ht0b, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h0, h240, h5, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p250_1, u0elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h3, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h6, hlam, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h218, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h219, hlam, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                    · linarith only [h2, h244, h249, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h219, h238, h248, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h218, h220, h247, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
              · linarith only [h0, h279, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                  · linarith only [h0, h244, h282, h5, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h218, h219, h238, h282, h7, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h218, h281, h7, hc23, hc34, hlam, hphi]
  · linarith only [h218, h219, h7, hlam]

end R2N4
