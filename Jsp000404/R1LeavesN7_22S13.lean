import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h10, h17, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h16, h20, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h11, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h10, h13, h16, h22, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h13, h15, h16, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
            · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h10, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h10, h14, h27, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
              · linarith only [h0, h27, h31, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                · linarith only [h13, h15, h27, h33, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h13, h15, h35, hlam]
                  · rcases h2bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h13, h15, h27, h4, h7, h9, hlam, p37_2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      rcases p37_3 (m.d 0 2) (by simp) with h41 | h41
                      · rcases p37_3 (m.d 1 2) (by simp) with h42 | h42
                        · linarith only [h0, h42, hlam]
                        · linarith only [h11, h42, hlam]
                      · linarith only [h41, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      rcases p37_3 (m.d 0 2) (by simp) with h46 | h46
                      · rcases p37_3 (m.d 1 2) (by simp) with h47 | h47
                        · linarith only [h0, h47, hlam]
                        · linarith only [h12, h47, hlam]
                      · linarith only [h46, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      rcases p37_3 (m.d 0 2) (by simp) with h53 | h53
                      · rcases p37_3 (m.d 1 2) (by simp) with h54 | h54
                        · rcases p37_3 (m.d 2 3) (by simp) with h55 | h55
                          · linarith only [h55, hlam, p37_0]
                          · rcases p37_3 (m.d 2 4) (by simp) with h57 | h57
                            · linarith only [h11, h57, hlam]
                            · linarith only [h27, h57, hlam]
                        · linarith only [h54, hlam, p37_0]
                      · linarith only [h4, h53, hlam]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      rcases p37_3 (m.d 0 2) (by simp) with h62 | h62
                      · rcases p37_3 (m.d 1 2) (by simp) with h63 | h63
                        · rcases p37_3 (m.d 2 3) (by simp) with h64 | h64
                          · linarith only [h10, h64, hlam]
                          · rcases p37_3 (m.d 2 4) (by simp) with h66 | h66
                            · linarith only [h66, hlam, p37_0]
                            · rcases p37_3 (m.d 2 5) (by simp) with h68 | h68
                              · linarith only [h12, h68, hlam]
                              · linarith only [h33, h68, hlam]
                        · linarith only [h63, hlam, p37_0]
                      · linarith only [h5, h62, hlam]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h4, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h10, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h27, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h31, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h5, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h11, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h33, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h6, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h12, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h1, h14, h31, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
          · linarith only [h0, h13, h14, h4, h8, h89, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
            · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
              · linarith only [h0, h10, h14, h92, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                · linarith only [h0, h11, h89, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h10, h11, h14, h89, h91, h96, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases h2bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi2]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 2) (by simp) with h101 | h101
                      · rcases p98_3 (m.d 1 2) (by simp) with h102 | h102
                        · linarith only [h0, h102, hlam]
                        · linarith only [h10, h102, hlam]
                      · linarith only [h101, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 2) (by simp) with h106 | h106
                      · rcases p98_3 (m.d 1 2) (by simp) with h107 | h107
                        · linarith only [h0, h107, hlam]
                        · linarith only [h107, h11, hlam]
                      · linarith only [h106, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 2) (by simp) with h111 | h111
                      · rcases p98_3 (m.d 1 2) (by simp) with h112 | h112
                        · linarith only [h0, h112, hlam]
                        · linarith only [h112, h12, hlam]
                      · linarith only [h111, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 2) (by simp) with h119 | h119
                      · rcases p98_3 (m.d 1 2) (by simp) with h120 | h120
                        · rcases p98_3 (m.d 2 3) (by simp) with h121 | h121
                          · linarith only [h10, h121, hlam]
                          · linarith only [h121, h91, hlam]
                        · linarith only [h120, hlam, p98_0]
                      · linarith only [h119, h5, hlam]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h91, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h4, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h10, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h92, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h5, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h11, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h91, hlam, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h94, hlam, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h6, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h12, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h12, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
            · linarith only [h13, h14, h91, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h143 | h143
        · linarith only [h0, h13, h143, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
          · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
            · linarith only [h0, h10, h13, h146, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
              · linarith only [h10, h143, h148, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                · linarith only [h0, h11, h150, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h152 | h152
                  · rcases h2bigk with h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h0, h11, h145, h150, hc01, hlam, hphi, ht0b, ht5b, p153_1, u5ehi2]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h13, h145, h146, h150, h4, h7, hlam, p153_2]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h13, h145, h150, h4, h7, hlam, p153_2]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      rcases p153_3 (m.d 0 2) (by simp) with h158 | h158
                      · rcases p153_3 (m.d 1 2) (by simp) with h159 | h159
                        · linarith only [h0, h159, hlam]
                        · linarith only [h12, h159, hlam]
                      · linarith only [h158, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h0, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      rcases p153_3 (m.d 0 2) (by simp) with h165 | h165
                      · rcases p153_3 (m.d 1 2) (by simp) with h166 | h166
                        · rcases p153_3 (m.d 2 3) (by simp) with h167 | h167
                          · linarith only [h167, hlam, p153_0]
                          · rcases p153_3 (m.d 2 4) (by simp) with h169 | h169
                            · linarith only [h11, h169, hlam]
                            · linarith only [h146, h169, hlam]
                        · linarith only [h166, hlam, p153_0]
                      · linarith only [h165, h4, hlam]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      rcases p153_3 (m.d 0 2) (by simp) with h174 | h174
                      · rcases p153_3 (m.d 1 2) (by simp) with h175 | h175
                        · rcases p153_3 (m.d 2 3) (by simp) with h176 | h176
                          · linarith only [h10, h176, hlam]
                          · rcases p153_3 (m.d 2 4) (by simp) with h178 | h178
                            · linarith only [h178, hlam, p153_0]
                            · rcases p153_3 (m.d 2 5) (by simp) with h180 | h180
                              · linarith only [h12, h180, hlam]
                              · linarith only [h150, h180, hlam]
                        · linarith only [h175, hlam, p153_0]
                      · linarith only [h174, h5, hlam]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p153_1, u5ehi2]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h4, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h10, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h146, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h148, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h5, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h11, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h0, h13, h145, h150, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h150, hlam, p153_1]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h6, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h12, hlam, p153_0]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [h0, h13, h145, h150, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p153_1]
                    · have p153_0 := h153c.1
                      have p153_1 := h153c.2.1
                      have p153_2 := h153c.2.2.1
                      have p153_3 := h153c.2.2.2
                      linarith only [hlam, p153_0]
                  · linarith only [h13, h145, h152, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
            · linarith only [h10, h13, h202, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
              · linarith only [h10, h143, h204, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                · linarith only [h0, h11, h145, h206, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                  · rcases h2bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p209_1, u5ehi2]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h10, h13, h145, h208, h4, h7, hlam, p209_2]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h11, h145, h208, h4, h7, hlam, p209_2]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      rcases p209_3 (m.d 0 2) (by simp) with h214 | h214
                      · rcases p209_3 (m.d 1 2) (by simp) with h215 | h215
                        · linarith only [h0, h215, hlam]
                        · linarith only [h12, h215, hlam]
                      · linarith only [h214, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      rcases p209_3 (m.d 0 2) (by simp) with h221 | h221
                      · rcases p209_3 (m.d 1 2) (by simp) with h222 | h222
                        · rcases p209_3 (m.d 2 3) (by simp) with h223 | h223
                          · linarith only [h223, hlam, p209_0]
                          · rcases p209_3 (m.d 2 4) (by simp) with h225 | h225
                            · linarith only [h11, h225, hlam]
                            · linarith only [h202, h225, hlam]
                        · linarith only [h222, hlam, p209_0]
                      · linarith only [h221, h4, hlam]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      rcases p209_3 (m.d 0 2) (by simp) with h230 | h230
                      · rcases p209_3 (m.d 1 2) (by simp) with h231 | h231
                        · rcases p209_3 (m.d 2 3) (by simp) with h232 | h232
                          · linarith only [h10, h232, hlam]
                          · rcases p209_3 (m.d 2 4) (by simp) with h234 | h234
                            · linarith only [h234, hlam, p209_0]
                            · rcases p209_3 (m.d 2 5) (by simp) with h236 | h236
                              · linarith only [h12, h236, hlam]
                              · linarith only [h206, h236, hlam]
                        · linarith only [h231, hlam, p209_0]
                      · linarith only [h230, h5, hlam]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p209_1, u5ehi2]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h4, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h10, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h202, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h204, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h5, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h11, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h206, hlam, p209_1]
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
                      linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h12, h145, h208, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                  · rcases h2bigk with h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p257_1, u5ehi2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h10, h13, h208, h4, h7, h9, hlam, p257_2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      rcases p257_3 (m.d 0 2) (by simp) with h261 | h261
                      · rcases p257_3 (m.d 1 2) (by simp) with h262 | h262
                        · linarith only [h0, h262, hlam]
                        · linarith only [h11, h262, hlam]
                      · linarith only [h261, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      rcases p257_3 (m.d 0 2) (by simp) with h266 | h266
                      · rcases p257_3 (m.d 1 2) (by simp) with h267 | h267
                        · linarith only [h0, h267, hlam]
                        · linarith only [h12, h267, hlam]
                      · linarith only [h266, hlam, p257_0]
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
                      rcases p257_3 (m.d 0 2) (by simp) with h273 | h273
                      · rcases p257_3 (m.d 1 2) (by simp) with h274 | h274
                        · rcases p257_3 (m.d 2 3) (by simp) with h275 | h275
                          · linarith only [h275, hlam, p257_0]
                          · rcases p257_3 (m.d 2 4) (by simp) with h277 | h277
                            · linarith only [h11, h277, hlam]
                            · linarith only [h202, h277, hlam]
                        · linarith only [h274, hlam, p257_0]
                      · linarith only [h273, h4, hlam]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      rcases p257_3 (m.d 0 2) (by simp) with h282 | h282
                      · rcases p257_3 (m.d 1 2) (by simp) with h283 | h283
                        · rcases p257_3 (m.d 2 3) (by simp) with h284 | h284
                          · linarith only [h10, h284, hlam]
                          · rcases p257_3 (m.d 2 4) (by simp) with h286 | h286
                            · linarith only [h286, hlam, p257_0]
                            · rcases p257_3 (m.d 2 5) (by simp) with h288 | h288
                              · linarith only [h12, h288, hlam]
                              · linarith only [h206, h288, hlam]
                        · linarith only [h283, hlam, p257_0]
                      · linarith only [h282, h5, hlam]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p257_1, u5ehi2]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h4, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h10, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h202, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h204, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h5, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h11, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h206, hlam, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h6, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h12, hlam, p257_0]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p257_1]
                    · have p257_0 := h257c.1
                      have p257_1 := h257c.2.1
                      have p257_2 := h257c.2.2.1
                      have p257_3 := h257c.2.2.2
                      linarith only [hlam, p257_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
      · rcases m.htr 1 3 5 (by decide) (by decide) with h310 | h310
        · linarith only [h0, h10, h12, h310, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h312 | h312
          · linarith only [h0, h10, h12, h309, h312, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
            · linarith only [h0, h10, h12, h314, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h12, h309, h314, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h317 | h317
        · linarith only [h0, h11, h12, h309, h317, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
          · linarith only [h0, h11, h12, h319, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
            · linarith only [h0, h10, h12, h309, h321, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
              · linarith only [h0, h10, h12, h317, h323, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                · linarith only [h0, h11, h12, h323, h325, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
                  · linarith only [h11, h12, h321, h325, h327, hc23, hc34, hlam, hphi]
                  · rcases h2bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      rcases p329_3 (m.d 0 2) (by simp) with h331 | h331
                      · rcases p329_3 (m.d 1 2) (by simp) with h332 | h332
                        · linarith only [h0, h332, hlam]
                        · rcases p329_3 (m.d 2 3) (by simp) with h334 | h334
                          · linarith only [h334, h4, hlam]
                          · rcases p329_3 (m.d 2 4) (by simp) with h336 | h336
                            · linarith only [h336, h5, hlam]
                            · rcases p329_3 (m.d 2 5) (by simp) with h338 | h338
                              · linarith only [h338, h6, hlam]
                              · linarith only [h12, h338, hlam]
                      · linarith only [h0, h331, hlam]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h11, h12, h321, h323, h327, h4, h7, h9, hlam, p329_2]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h11, h12, h323, h327, h4, h7, h9, hlam, p329_2]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h0, h11, h12, h321, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h0, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h12, h323, hc23, hc35, hlam, hphi, p329_1]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h0, h12, h321, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h12, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h4, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h10, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h321, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h323, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h5, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h11, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h0, h11, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h325, hlam, p329_1]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h6, hlam, p329_0]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p329_1]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      rcases p329_3 (m.d 0 2) (by simp) with h362 | h362
                      · rcases p329_3 (m.d 1 2) (by simp) with h363 | h363
                        · linarith only [h12, h363, hlam]
                        · linarith only [h10, h363, hlam]
                      · linarith only [h362, h4, hlam]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      rcases p329_3 (m.d 0 2) (by simp) with h367 | h367
                      · rcases p329_3 (m.d 1 2) (by simp) with h368 | h368
                        · linarith only [h12, h368, hlam]
                        · linarith only [h11, h368, hlam]
                      · linarith only [h367, h5, hlam]
                    · have p329_0 := h329c.1
                      have p329_1 := h329c.2.1
                      have p329_2 := h329c.2.2.1
                      have p329_3 := h329c.2.2.2
                      linarith only [hlam, p329_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h373 | h373
    · linarith only [h0, h11, h373, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h375 | h375
      · linarith only [h10, h11, h375, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
        · linarith only [h0, h10, h11, h377, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
          · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
            · linarith only [h0, h10, h11, h375, h380, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
              · linarith only [h10, h373, h377, h382, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                · rcases m.htr 3 4 5 (by decide) (by decide) with h385 | h385
                  · rcases h2bigk with h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      rcases p386_3 (m.d 0 2) (by simp) with h388 | h388
                      · rcases p386_3 (m.d 1 2) (by simp) with h389 | h389
                        · linarith only [h0, h389, hlam]
                        · rcases p386_3 (m.d 2 3) (by simp) with h391 | h391
                          · linarith only [h391, h4, hlam]
                          · rcases p386_3 (m.d 2 4) (by simp) with h393 | h393
                            · linarith only [h393, h5, hlam]
                            · linarith only [h11, h393, hlam]
                      · linarith only [h0, h388, hlam]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h10, h373, h380, h384, h4, h7, hlam, p386_2]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h0, h10, h373, h384, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p386_1]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h0, h10, h373, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p386_1]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h0, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h373, h382, hc23, hc35, hlam, hphi, p386_1]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h11, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h373, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h4, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h10, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h380, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h382, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h5, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p386_1]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      rcases p386_3 (m.d 0 2) (by simp) with h412 | h412
                      · rcases p386_3 (m.d 1 2) (by simp) with h413 | h413
                        · linarith only [h11, h413, hlam]
                        · linarith only [h10, h413, hlam]
                      · linarith only [h4, h412, hlam]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h0, h380, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p386_1, u5ehi2]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h6, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p386_1]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      rcases p386_3 (m.d 0 2) (by simp) with h421 | h421
                      · rcases p386_3 (m.d 1 2) (by simp) with h422 | h422
                        · linarith only [h373, h422, hlam]
                        · linarith only [h10, h422, hlam]
                      · linarith only [h4, h421, hlam]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [h384, hlam, p386_0]
                    · have p386_0 := h386c.1
                      have p386_1 := h386c.2.1
                      have p386_2 := h386c.2.2.1
                      have p386_3 := h386c.2.2.2
                      linarith only [hlam, p386_0]
                  · linarith only [h10, h11, h2, h379, h380, h385, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h11, h379, h384, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
            · linarith only [h0, h10, h11, h430, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
              · linarith only [h0, h10, h11, h379, h4, h432, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                · linarith only [h0, h10, h11, h379, h4, h430, h434, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h10, h11, h4, h434, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
