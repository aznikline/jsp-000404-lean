import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h10, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h12, h15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h10, h18, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h12, h18, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h12, h13, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
            · linarith only [h0, h12, h22, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h12, h25, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                  · linarith only [h10, h22, h27, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h11, h29, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h2, h24, h29, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                · linarith only [h0, h10, h32, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h0, h10, h12, h24, h34, h4, h7, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h0, h12, h24, h36, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                      · linarith only [h0, h10, h12, h24, h38, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h10, h12, h38, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
        · linarith only [h0, h10, h4, h42, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
          · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
            · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h1, h44, h50, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h2, h46, h50, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h42, h46, h49, hlam]
                  · linarith only [h10, h45, h48, hlam]
                · linarith only [h0, h10, h4, h45, h47, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h4, h46, h56, h58, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h0, h4, h42, h58, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h10, h4, h57, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h10, h44, h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h4, h44, h45, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
            · linarith only [h0, h4, h44, h64, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                · linarith only [h0, h4, h44, h67, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h4, h67, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · linarith only [h0, h10, h4, h44, h70, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h4, h7, h70, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
      · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
        · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
          · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
              · linarith only [h2, h77, h9, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                · linarith only [h0, h73, h79, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h75, h79, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h4, h75, h76, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
            · linarith only [h0, h4, h7, h75, h83, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
              · linarith only [h2, h85, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h4, h75, h87, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                  · linarith only [h73, h83, h89, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
                    · linarith only [h0, h5, h73, h8, h83, h9, h91, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h7, h9, h93, hlam]
                      · rcases h0bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h74, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, h73, h75, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, h73, h75, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, h73, h75, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, h73, h75, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p95_1, u0elo1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h7, h73, h75, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h7, h73, h75, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h1, hlam, p95_1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h4, hlam, p95_1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, h73, h75, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p95_1, u0elo2]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h0, h4, h7, h73, h75, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h2, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h5, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h9, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h3, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h6, hlam, p95_1]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h8, hlam, p95_0]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [h7, h73, h75, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p95_1, u0elo4]
                        · have p95_0 := h95c.1
                          have p95_1 := h95c.2.1
                          have p95_2 := h95c.2.2.1
                          have p95_3 := h95c.2.2.2
                          linarith only [hlam, p95_0]
        · linarith only [h0, h5, h73, h74, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
        · linarith only [h0, h122, h4, h73, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
          · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
            · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
              · linarith only [h122, h126, h5, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                    · linarith only [h130, h5, h9, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h124, h132, h9, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases h0bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, h73, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h1, h125, hc35, hlam, hphi, ht01, ht0b, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h122, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h122, h5, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h0, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h1, h125, hc35, hlam, hphi, ht0b, ht5b, p134_1, u0elo1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h0, h122, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h0, h122, h5, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h1, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h122, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u0elo2]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h0, h122, h4, h5, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h2, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h5, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h7, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h9, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h3, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h6, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h8, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h122, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u0elo4]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                  · linarith only [h0, h122, h128, h129, h4, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1, h124, h128, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h124, h125, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
            · linarith only [h0, h124, h163, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
              · linarith only [h165, h2, h9, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                · linarith only [h0, h124, h167, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h167, h4, h7, h73, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h170 | h170
    · linarith only [h170, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
      · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
          · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
            · linarith only [h1, h175, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
              · linarith only [h1, h170, h174, h177, h2, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                · linarith only [h0, h172, h179, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h174, h179, h8, hc23, hc35, hlam, hphi]
          · linarith only [h174, h7, h8, hc13, hc35, hlam, hphi]
        · linarith only [h0, h172, h173, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
        · linarith only [h0, h172, h184, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
          · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
            · linarith only [h0, h172, h187, h4, h8, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
              · linarith only [h170, h184, h189, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                  · linarith only [h184, h192, h5, h7, h8, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h170, h194, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                      · linarith only [h170, h184, h186, h196, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases h0bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h172, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p198_1, u1elo0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h184, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p198_1, u1elo0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h184, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p198_1, u1elo0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h184, h5, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p198_1, u1elo0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h0, hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h184, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p198_1, u0elo1]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h0, h184, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p198_1, u1elo0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h0, h184, h5, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p198_1, u1elo0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h1, hlam, p198_1]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h4, hlam, p198_1]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h184, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p198_1, u0elo2]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h8, hlam, p198_1]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h2, hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h5, hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h7, hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h170, hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h3, hlam, p198_0]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h6, hlam, p198_1]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h1, h186, hc34, hlam, hphi, ht0b, ht45, ht5b, p198_1, u0elo4]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [h184, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p198_1, u0elo4]
                        · have p198_0 := h198c.1
                          have p198_1 := h198c.2.1
                          have p198_2 := h198c.2.2.1
                          have p198_3 := h198c.2.2.2
                          linarith only [hlam, p198_0]
                · linarith only [h172, h186, h191, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · linarith only [h186, h7, h8, hc13, hc35, hlam, hphi]

end R2N4
