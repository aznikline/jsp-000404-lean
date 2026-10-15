import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h10, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h10, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h10, h11, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h10, h20, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h10, h23, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h20, h25, h7, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                      · rcases h1bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          rcases p28_3 (m.d 0 1) (by simp) with h31 | h31
                          · rcases p28_3 (m.d 1 2) (by simp) with h32 | h32
                            · linarith only [h0, h32, hlam]
                            · linarith only [h32, h7, hlam]
                          · linarith only [h31, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          rcases p28_3 (m.d 0 1) (by simp) with h36 | h36
                          · rcases p28_3 (m.d 1 2) (by simp) with h37 | h37
                            · linarith only [h0, h37, hlam]
                            · linarith only [h37, h8, hlam]
                          · linarith only [h36, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          rcases p28_3 (m.d 0 1) (by simp) with h41 | h41
                          · rcases p28_3 (m.d 1 2) (by simp) with h42 | h42
                            · linarith only [h0, h42, hlam]
                            · linarith only [h42, h9, hlam]
                          · linarith only [h41, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h20, h22, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h20, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h1, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h7, hlam, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h10, hlam, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h20, hlam, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h2, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h8, hlam, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h2, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h10, h20, h4, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h3, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h9, hlam, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h22, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                      · linarith only [h10, h27, h7, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                  · linarith only [h10, h67, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                    · linarith only [h10, h69, h7, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h10, h22, h4, h5, h7, h71, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h10, h7, h71, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
              · linarith only [h7, h75, h9, hlam]
              · linarith only [h0, h4, h6, h74, h75, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
              · linarith only [h74, h78, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                · linarith only [h8, h80, h9, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h4, h74, h82, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h7, h74, h84, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h8, h82, h84, h9, hc35, hlam, hphi, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
          · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
            · linarith only [h7, h8, h88, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
              · linarith only [h0, h4, h5, h88, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                  · linarith only [h0, h4, h88, h93, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h4, h5, h7, h8, h93, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h7, h8, h92, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
            · linarith only [h7, h8, h97, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
              · linarith only [h0, h4, h5, h97, h99, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                  · linarith only [h0, h102, h4, h97, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h102, h4, h5, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h101, h7, h8, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
        · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
          · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                  · linarith only [h0, h106, h111, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h106, h108, h111, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                  · linarith only [h0, h106, h114, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h108, h110, h114, h7, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h108, h109, hc35, hlam, hphi, u3ehi3]
            · linarith only [h106, h108, h7, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
            · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                · linarith only [h106, h107, h121, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                  · linarith only [h0, h106, h123, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h106, h119, h123, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h119, h120, h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h106, h119, h7, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
          · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
            · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
              · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                    · linarith only [h0, h106, h128, h132, h133, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h0, h106, h128, h132, h133, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h128, h129, h130, h132, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h106, h128, h131, hlam]
              · linarith only [h0, h129, h130, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
              · linarith only [h129, h139, hc34, hlam, hphi, u3ehi4]
              · linarith only [h128, h139, h7, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 3 5 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h147 | h147
                      · rcases h1bigk with h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 1) (by simp) with h150 | h150
                          · rcases p148_3 (m.d 1 2) (by simp) with h151 | h151
                            · linarith only [h151, hlam, p148_0]
                            · rcases p148_3 (m.d 1 3) (by simp) with h153 | h153
                              · linarith only [h1, h153, hlam]
                              · linarith only [h153, h7, hlam]
                          · linarith only [h150, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h142, h147, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1, u3ehi4]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 1) (by simp) with h158 | h158
                          · rcases p148_3 (m.d 1 2) (by simp) with h159 | h159
                            · linarith only [h0, h159, hlam]
                            · rcases p148_3 (m.d 1 3) (by simp) with h161 | h161
                              · linarith only [h1, h161, hlam]
                              · linarith only [h142, h161, hlam]
                          · linarith only [h158, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 1) (by simp) with h165 | h165
                          · rcases p148_3 (m.d 1 2) (by simp) with h166 | h166
                            · linarith only [h0, h166, hlam]
                            · rcases p148_3 (m.d 1 3) (by simp) with h168 | h168
                              · linarith only [h1, h168, hlam]
                              · linarith only [h143, h168, hlam]
                          · linarith only [h165, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h0, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h7, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h106, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h128, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h1, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 1) (by simp) with h178 | h178
                          · rcases p148_3 (m.d 1 2) (by simp) with h179 | h179
                            · linarith only [h179, h7, hlam]
                            · rcases p148_3 (m.d 1 3) (by simp) with h181 | h181
                              · rcases p148_3 (m.d 1 4) (by simp) with h182 | h182
                                · linarith only [h142, h182, hlam]
                                · linarith only [h106, h182, hlam]
                              · linarith only [h181, h7, hlam]
                          · linarith only [h0, h178, hlam]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h0, h142, h147, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1, u3ehi4]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h0, h143, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1, u3ehi4]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h2, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 1) (by simp) with h191 | h191
                          · rcases p148_3 (m.d 1 2) (by simp) with h192 | h192
                            · linarith only [h106, h192, hlam]
                            · rcases p148_3 (m.d 1 3) (by simp) with h194 | h194
                              · rcases p148_3 (m.d 1 4) (by simp) with h195 | h195
                                · rcases p148_3 (m.d 1 5) (by simp) with h196 | h196
                                  · linarith only [h144, h196, hlam]
                                  · linarith only [h128, h196, hlam]
                                · linarith only [h106, h195, hlam]
                              · linarith only [h194, h7, hlam]
                          · linarith only [h0, h191, hlam]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h142, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h0, h106, h143, h145, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p148_1, u3ehi4]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h3, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 1) (by simp) with h206 | h206
                          · rcases p148_3 (m.d 1 2) (by simp) with h207 | h207
                            · linarith only [h128, h207, hlam]
                            · rcases p148_3 (m.d 1 3) (by simp) with h209 | h209
                              · rcases p148_3 (m.d 1 4) (by simp) with h210 | h210
                                · rcases p148_3 (m.d 1 5) (by simp) with h211 | h211
                                  · rcases h3bigk with h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, h142, h147, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p212_1, u3ehi4]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, h106, h144, h145, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p148_1, p212_1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 3) (by simp) with h216 | h216
                                      · rcases p212_3 (m.d 1 3) (by simp) with h217 | h217
                                        · linarith only [h1, h217, hlam]
                                        · linarith only [h142, h217, hlam]
                                      · linarith only [h216, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 3) (by simp) with h221 | h221
                                      · rcases p212_3 (m.d 1 3) (by simp) with h222 | h222
                                        · linarith only [h1, h222, hlam]
                                        · linarith only [h143, h222, hlam]
                                      · linarith only [h221, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h1, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h7, hlam, p212_1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h1, h147, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p212_1, u3ehi4]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p212_1, u3ehi4]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h4, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p212_1, u3ehi1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, h147, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p212_1, u3ehi4]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p212_1, u3ehi4]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h5, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h142, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h145, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hc34, hlam, hphi, p212_1, u3ehi4]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h6, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h143, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h146, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h147, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                  · linarith only [h128, h211, hlam]
                                · linarith only [h106, h210, hlam]
                              · linarith only [h209, h7, hlam]
                          · linarith only [h0, h206, hlam]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h143, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h144, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                      · linarith only [h0, h142, h144, h147, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h142, h146, h4, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h142, h145, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                      · linarith only [h1, h142, h144, h258, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h1bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 1) (by simp) with h262 | h262
                          · rcases p260_3 (m.d 1 2) (by simp) with h263 | h263
                            · linarith only [h263, hlam, p260_0]
                            · rcases p260_3 (m.d 1 3) (by simp) with h265 | h265
                              · linarith only [h1, h265, hlam]
                              · linarith only [h265, h7, hlam]
                          · linarith only [h262, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h143, h258, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi3]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 1) (by simp) with h270 | h270
                          · rcases p260_3 (m.d 1 2) (by simp) with h271 | h271
                            · linarith only [h0, h271, hlam]
                            · rcases p260_3 (m.d 1 3) (by simp) with h273 | h273
                              · linarith only [h1, h273, hlam]
                              · linarith only [h142, h273, hlam]
                          · linarith only [h270, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 1) (by simp) with h277 | h277
                          · rcases p260_3 (m.d 1 2) (by simp) with h278 | h278
                            · linarith only [h0, h278, hlam]
                            · rcases p260_3 (m.d 1 3) (by simp) with h280 | h280
                              · linarith only [h1, h280, hlam]
                              · linarith only [h143, h280, hlam]
                          · linarith only [h277, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h0, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h7, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h106, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h128, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h1, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 1) (by simp) with h290 | h290
                          · rcases p260_3 (m.d 1 2) (by simp) with h291 | h291
                            · linarith only [h291, h7, hlam]
                            · rcases p260_3 (m.d 1 3) (by simp) with h293 | h293
                              · rcases p260_3 (m.d 1 4) (by simp) with h294 | h294
                                · linarith only [h142, h294, hlam]
                                · linarith only [h106, h294, hlam]
                              · linarith only [h293, h7, hlam]
                          · linarith only [h0, h290, hlam]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h0, h142, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi3]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h0, h142, h144, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi3]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h2, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h144, hc12, hc45, hlam, hphi, ht23, ht34, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h142, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h144, hlam, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h3, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 1) (by simp) with h308 | h308
                          · rcases p260_3 (m.d 1 2) (by simp) with h309 | h309
                            · linarith only [h128, h309, hlam]
                            · rcases p260_3 (m.d 1 3) (by simp) with h311 | h311
                              · rcases p260_3 (m.d 1 4) (by simp) with h312 | h312
                                · linarith only [h144, h312, hlam]
                                · linarith only [h106, h312, hlam]
                              · linarith only [h311, h7, hlam]
                          · linarith only [h0, h308, hlam]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h143, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h142, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u3ehi3]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                    · linarith only [h0, h142, h257, h4, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h142, h256, h7, hlam]
              · linarith only [h142, h143, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
              · linarith only [h0, h142, h323, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
                · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                  · linarith only [h0, h142, h326, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                    · linarith only [h323, h326, h328, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                      · rcases h1bigk with h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h0, h328, h330, h4, h5, h7, hlam, p331_2]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h334 | h334
                          · rcases p331_3 (m.d 1 2) (by simp) with h335 | h335
                            · linarith only [h0, h335, hlam]
                            · rcases p331_3 (m.d 1 3) (by simp) with h337 | h337
                              · linarith only [h337, hlam, p331_0]
                              · rcases p331_3 (m.d 1 4) (by simp) with h339 | h339
                                · linarith only [h2, h339, hlam]
                                · linarith only [h142, h339, hlam]
                          · linarith only [h334, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h343 | h343
                          · rcases p331_3 (m.d 1 2) (by simp) with h344 | h344
                            · linarith only [h0, h344, hlam]
                            · rcases p331_3 (m.d 1 3) (by simp) with h346 | h346
                              · linarith only [h1, h346, hlam]
                              · rcases p331_3 (m.d 1 4) (by simp) with h348 | h348
                                · linarith only [h348, hlam, p331_0]
                                · rcases p331_3 (m.d 1 5) (by simp) with h350 | h350
                                  · linarith only [h3, h350, hlam]
                                  · rcases h3bigk with h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      rcases p352_3 (m.d 0 3) (by simp) with h354 | h354
                                      · rcases p352_3 (m.d 1 3) (by simp) with h355 | h355
                                        · linarith only [h1, h355, hlam]
                                        · rcases p352_3 (m.d 2 3) (by simp) with h357 | h357
                                          · linarith only [h357, h4, hlam]
                                          · linarith only [h357, h7, hlam]
                                      · linarith only [h1, h354, hlam]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      rcases p352_3 (m.d 0 3) (by simp) with h361 | h361
                                      · rcases p352_3 (m.d 1 3) (by simp) with h362 | h362
                                        · linarith only [h1, h362, hlam]
                                        · rcases p352_3 (m.d 2 3) (by simp) with h364 | h364
                                          · linarith only [h364, h4, hlam]
                                          · rcases p352_3 (m.d 3 4) (by simp) with h366 | h366
                                            · linarith only [h366, h5, hlam]
                                            · linarith only [h326, h366, hlam]
                                      · linarith only [h361, h4, hlam]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h0, h328, h330, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p352_1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h0, h328, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p352_1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h1, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h7, hlam, p352_1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h142, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h323, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h4, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h328, h330, hc34, hlam, hphi, p352_1, u3ehi1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h326, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h328, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h5, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p352_1, u3ehi1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p352_1, u3ehi2]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p352_1, u3ehi4]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h6, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [hc35, hlam, hphi, p352_1, u3ehi1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p352_1]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [h330, hlam, p352_0]
                                    · have p352_0 := h352c.1
                                      have p352_1 := h352c.2.1
                                      have p352_2 := h352c.2.2.1
                                      have p352_3 := h352c.2.2.2
                                      linarith only [hlam, p352_0]
                          · linarith only [h343, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h393 | h393
                          · rcases p331_3 (m.d 1 2) (by simp) with h394 | h394
                            · linarith only [h0, h394, hlam]
                            · rcases p331_3 (m.d 1 3) (by simp) with h396 | h396
                              · linarith only [h1, h396, hlam]
                              · rcases p331_3 (m.d 1 4) (by simp) with h398 | h398
                                · linarith only [h2, h398, hlam]
                                · linarith only [h325, h398, hlam]
                          · linarith only [h393, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h0, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h7, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h106, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h128, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h1, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h0, h142, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h142, hlam, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h323, hlam, p331_1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h2, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h413 | h413
                          · rcases p331_3 (m.d 1 2) (by simp) with h414 | h414
                            · linarith only [h106, h414, hlam]
                            · rcases p331_3 (m.d 1 3) (by simp) with h416 | h416
                              · linarith only [h142, h416, hlam]
                              · linarith only [h416, h7, hlam]
                          · linarith only [h0, h413, hlam]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1, u3ehi1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h0, h142, h323, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1, u3ehi1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h3, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          rcases p331_3 (m.d 0 1) (by simp) with h424 | h424
                          · rcases p331_3 (m.d 1 2) (by simp) with h425 | h425
                            · linarith only [h128, h425, hlam]
                            · rcases p331_3 (m.d 1 3) (by simp) with h427 | h427
                              · linarith only [h323, h427, hlam]
                              · linarith only [h427, h7, hlam]
                          · linarith only [h0, h424, hlam]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1, u3ehi1]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [h325, hlam, p331_0]
                        · have p331_0 := h331c.1
                          have p331_1 := h331c.2.1
                          have p331_2 := h331c.2.2.1
                          have p331_3 := h331c.2.2.2
                          linarith only [hlam, p331_0]
                      · linarith only [h106, h325, h326, h330, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                  · linarith only [h0, h142, h4, h435, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
                    · linarith only [h435, h437, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                      · linarith only [h0, h142, h325, h4, h439, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h435, h439, hc45, hlam, hphi, ht34, u3ehi2]
    · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h443 | h443
    · linarith only [h443, h5, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
      · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
        · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
          · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
            · linarith only [h1, h448, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h450 | h450
              · linarith only [h1, h450, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h452 | h452
                · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                  · linarith only [h445, h453, h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                    · linarith only [h1, h443, h445, h455, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                      · rcases h1bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h445, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          rcases p458_3 (m.d 0 1) (by simp) with h461 | h461
                          · rcases p458_3 (m.d 1 2) (by simp) with h462 | h462
                            · linarith only [h0, h462, hlam]
                            · linarith only [h445, h462, hlam]
                          · linarith only [h461, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          rcases p458_3 (m.d 0 1) (by simp) with h466 | h466
                          · rcases p458_3 (m.d 1 2) (by simp) with h467 | h467
                            · linarith only [h0, h467, hlam]
                            · linarith only [h446, h467, hlam]
                          · linarith only [h466, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          rcases p458_3 (m.d 0 1) (by simp) with h471 | h471
                          · rcases p458_3 (m.d 1 2) (by simp) with h472 | h472
                            · linarith only [h0, h472, hlam]
                            · linarith only [h447, h472, hlam]
                          · linarith only [h471, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h445, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h452, hc01, hc45, hlam, hphi, ht0b, ht5b, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h0, h445, h450, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h1, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h445, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h448, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h450, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h2, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h446, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h2, h445, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h2, h445, h450, h5, hc34, hlam, hphi, p458_1, u3ehi2]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h3, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h447, hlam, p458_1]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h3, h445, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [h452, hlam, p458_0]
                        · have p458_0 := h458c.1
                          have p458_1 := h458c.2.1
                          have p458_2 := h458c.2.2.1
                          have p458_3 := h458c.2.2.2
                          linarith only [hlam, p458_0]
                      · linarith only [h1, h445, h457, h5, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h497 | h497
                  · linarith only [h1, h445, h497, h5, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                    · linarith only [h1, h443, h445, h499, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h501 | h501
                      · linarith only [h445, h448, h452, h501, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1, h445, h5, h501, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
            · linarith only [h1, h5, h504, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
              · linarith only [h1, h3, h443, h445, h447, h5, h506, hc34, hlam, hphi, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
                · linarith only [h446, h447, h508, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
                  · linarith only [h3, h445, h447, h5, h510, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                    · linarith only [h3, h443, h446, h447, h510, h512, hlam]
                    · linarith only [h446, h447, h510, h512, hc35, hlam, hphi, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
          · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
            · linarith only [h1, h2, h445, h446, h5, h516, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h518 | h518
              · linarith only [h1, h5, h518, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h520 | h520
                · rcases m.htr 2 3 4 (by decide) (by decide) with h521 | h521
                  · linarith only [h2, h445, h446, h5, h521, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h445, h446, h521, hc34, hlam, hphi, u3ehi2]
                · linarith only [h445, h446, h520, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
            · linarith only [h1, h5, h525, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
              · linarith only [h1, h443, h527, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                  · linarith only [h2, h445, h5, h515, h529, h530, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h445, h446, h530, hc34, hlam, hphi, u3ehi2]
                · linarith only [h445, h446, h529, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
        · rcases m.htr 1 2 5 (by decide) (by decide) with h535 | h535
          · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
            · linarith only [h4, h445, h5, h536, hlam]
            · linarith only [h4, h445, h5, h534, h536, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
            · linarith only [h4, h445, h5, h534, h539, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h4, h445, h5, h534, h539, hc34, hlam, hphi, u3ehi1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h542 | h542
          · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
            · linarith only [h4, h445, h5, h542, h543, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h545 | h545
              · linarith only [h4, h445, h5, h545, hc34, hlam, hphi, u3ehi4]
              · linarith only [h4, h445, h5, h542, h545, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
            · linarith only [h1, h4, h445, h5, h548, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
              · linarith only [h1, h4, h443, h445, h550, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
                · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                  · linarith only [h4, h5, h553, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                    · linarith only [h4, h443, h555, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h557 | h557
                      · rcases h1bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 1) (by simp) with h560 | h560
                          · rcases p558_3 (m.d 1 2) (by simp) with h561 | h561
                            · linarith only [h561, hlam, p558_0]
                            · rcases p558_3 (m.d 1 3) (by simp) with h563 | h563
                              · linarith only [h1, h563, hlam]
                              · linarith only [h445, h563, hlam]
                          · linarith only [h560, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 1) (by simp) with h567 | h567
                          · rcases p558_3 (m.d 1 2) (by simp) with h568 | h568
                            · linarith only [h0, h568, hlam]
                            · rcases p558_3 (m.d 1 3) (by simp) with h570 | h570
                              · linarith only [h570, hlam, p558_0]
                              · rcases p558_3 (m.d 1 4) (by simp) with h572 | h572
                                · linarith only [h2, h572, hlam]
                                · linarith only [h548, h572, hlam]
                          · linarith only [h567, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 1) (by simp) with h576 | h576
                          · rcases p558_3 (m.d 1 2) (by simp) with h577 | h577
                            · linarith only [h0, h577, hlam]
                            · rcases p558_3 (m.d 1 3) (by simp) with h579 | h579
                              · linarith only [h1, h579, hlam]
                              · rcases p558_3 (m.d 1 4) (by simp) with h581 | h581
                                · linarith only [h581, hlam, p558_0]
                                · rcases p558_3 (m.d 1 5) (by simp) with h583 | h583
                                  · linarith only [h3, h583, hlam]
                                  · rcases h3bigk with h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h443, h557, hc34, hlam, hphi, p585_1, u3ehi1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h443, h445, h557, hc12, hc34, hlam, hphi, ht23, p585_1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h5, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h443, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h1, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h445, hlam, p585_1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h548, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h550, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h4, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p585_1, u3ehi1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h553, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h555, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hc34, hlam, hphi, p585_1, u3ehi0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hc34, hlam, hphi, p585_1, u3ehi1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h445, hc12, hc34, hlam, hphi, ht23, p585_1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hc34, hlam, hphi, p585_1, u3ehi4]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h4, h445, hc12, hc35, hlam, hphi, ht23, p585_1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hc35, hlam, hphi, p585_1, u3ehi1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h445, hc12, hc35, hlam, hphi, ht23, p585_1]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [h557, hlam, p585_0]
                                    · have p585_0 := h585c.1
                                      have p585_1 := h585c.2.1
                                      have p585_2 := h585c.2.2.1
                                      have p585_3 := h585c.2.2.2
                                      linarith only [hlam, p585_0]
                          · linarith only [h576, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 1) (by simp) with h612 | h612
                          · rcases p558_3 (m.d 1 2) (by simp) with h613 | h613
                            · linarith only [h0, h613, hlam]
                            · rcases p558_3 (m.d 1 3) (by simp) with h615 | h615
                              · linarith only [h1, h615, hlam]
                              · rcases p558_3 (m.d 1 4) (by simp) with h617 | h617
                                · linarith only [h2, h617, hlam]
                                · linarith only [h552, h617, hlam]
                          · linarith only [h612, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h0, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h445, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h534, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h542, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h1, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h1, h5, hc12, hc34, hlam, hphi, ht23, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h548, hlam, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h550, hlam, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h2, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 1) (by simp) with h632 | h632
                          · rcases p558_3 (m.d 1 2) (by simp) with h633 | h633
                            · linarith only [h534, h633, hlam]
                            · rcases p558_3 (m.d 1 3) (by simp) with h635 | h635
                              · linarith only [h548, h635, hlam]
                              · linarith only [h445, h635, hlam]
                          · linarith only [h0, h632, hlam]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h2, h550, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h3, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 1) (by simp) with h643 | h643
                          · rcases p558_3 (m.d 1 2) (by simp) with h644 | h644
                            · linarith only [h542, h644, hlam]
                            · rcases p558_3 (m.d 1 3) (by simp) with h646 | h646
                              · linarith only [h550, h646, hlam]
                              · linarith only [h445, h646, hlam]
                          · linarith only [h0, h643, hlam]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1, u3ehi1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h552, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                      · linarith only [h2, h552, h557, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
                  · linarith only [h4, h5, h654, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h656 | h656
                    · linarith only [h4, h5, h656, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h658 | h658
                      · linarith only [h548, h552, h658, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h5, h658, hc45, hlam, hphi, ht34, u3ehi0]

end R2N4
