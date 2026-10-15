import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h14, h17, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h14, h16, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h11, h13, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h11, h14, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h0, h13, h23, h25, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                      · linarith only [h10, h13, h27, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h24, h25, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h10, h13, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h10, h13, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h10, h13, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h0, hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h10, h13, h6, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h0, h10, h13, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h0, h10, h13, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h1, hlam, p29_1]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h3, hlam, p29_1]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h10, h13, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h0, h10, h13, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi1]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h4, hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h6, hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h0, h10, h13, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h2, hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h5, hlam, p29_1]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h7, hlam, p29_0]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [h8, hlam, p29_1]
                        · have p29_0 := h29c.1
                          have p29_1 := h29c.2.1
                          have p29_2 := h29c.2.2.1
                          have p29_3 := h29c.2.2.2
                          linarith only [hlam, p29_0]
                  · linarith only [h0, h12, h23, h24, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h11, h23, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
              · linarith only [h11, h12, h57, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h10, h11, h12, h60, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h10, h57, h62, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                      · linarith only [h10, h12, h57, h59, h64, h7, h9, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases h0bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h12, h3, h6, h64, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p66_1]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h12, h6, h64, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi2]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h10, h11, h12, h64, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h10, h11, h12, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h0, hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h10, h11, h12, h6, h64, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h0, h10, h11, h12, h64, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h0, h10, h11, h12, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h1, hlam, p66_1]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h3, hlam, p66_1]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h10, h11, h12, h64, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h0, h10, h11, h12, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi1]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h4, hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h6, hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h0, h10, h11, h12, h3, h6, h64, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi3]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h2, hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h5, hlam, p66_1]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h7, hlam, p66_0]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [h8, hlam, p66_1]
                        · have p66_0 := h66c.1
                          have p66_1 := h66c.2.1
                          have p66_2 := h66c.2.2.1
                          have p66_3 := h66c.2.2.2
                          linarith only [hlam, p66_0]
                · linarith only [h11, h12, h59, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
            · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
              · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                · linarith only [h0, h11, h3, h93, h95, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                      · rcases h0bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h3, h97, hc01, hc35, hlam, hphi, ht0b, ht5b, p100_1]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h11, h6, h9, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi4]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h11, h6, h9, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi4]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          rcases p100_3 (m.d 0 1) (by simp) with h105 | h105
                          · rcases p100_3 (m.d 0 2) (by simp) with h106 | h106
                            · linarith only [h0, h106, hlam]
                            · linarith only [h106, h5, hlam]
                          · linarith only [h105, h2, hlam]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h0, hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h11, h6, h9, h97, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi4]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h0, h11, h6, h9, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi4]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          rcases p100_3 (m.d 0 1) (by simp) with h114 | h114
                          · rcases p100_3 (m.d 0 2) (by simp) with h115 | h115
                            · rcases p100_3 (m.d 0 3) (by simp) with h116 | h116
                              · linarith only [h116, h3, hlam]
                              · linarith only [h116, h7, hlam]
                            · linarith only [h115, h5, hlam]
                          · linarith only [h114, h2, hlam]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h1, hlam, p100_1]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h3, hlam, p100_1]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h11, h6, h9, h97, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi4]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          rcases p100_3 (m.d 0 1) (by simp) with h125 | h125
                          · rcases p100_3 (m.d 0 2) (by simp) with h126 | h126
                            · rcases p100_3 (m.d 0 3) (by simp) with h127 | h127
                              · rcases p100_3 (m.d 0 4) (by simp) with h128 | h128
                                · linarith only [h128, h6, hlam]
                                · linarith only [h128, h8, hlam]
                              · linarith only [h127, h7, hlam]
                            · linarith only [h126, h5, hlam]
                          · linarith only [h125, h2, hlam]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi1]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h4, hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h6, hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          rcases p100_3 (m.d 0 1) (by simp) with h138 | h138
                          · rcases p100_3 (m.d 0 2) (by simp) with h139 | h139
                            · rcases p100_3 (m.d 0 3) (by simp) with h140 | h140
                              · rcases p100_3 (m.d 0 4) (by simp) with h141 | h141
                                · rcases p100_3 (m.d 0 5) (by simp) with h142 | h142
                                  · linarith only [h142, h8, hlam]
                                  · rcases h3bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h3, h9, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p144_1, u2ehi4]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h3, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p144_1, u2ehi4]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h11, h3, h9, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p144_1, u2ehi4]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      rcases p144_3 (m.d 0 3) (by simp) with h149 | h149
                                      · rcases p144_3 (m.d 1 3) (by simp) with h150 | h150
                                        · linarith only [h1, h150, hlam]
                                        · linarith only [h150, h93, hlam]
                                      · linarith only [h149, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h1, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h97, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p144_1, u2ehi4]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h11, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h11, h3, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h3, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h9, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h95, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h3, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h6, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h0, h3, h6, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h7, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h93, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h97, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h99, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                · linarith only [h141, h8, hlam]
                              · linarith only [h140, h7, hlam]
                            · linarith only [h139, h5, hlam]
                          · linarith only [h138, h2, hlam]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h2, hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h5, hlam, p100_1]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h7, hlam, p100_0]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [h8, hlam, p100_1]
                        · have p100_0 := h100c.1
                          have p100_1 := h100c.2.1
                          have p100_2 := h100c.2.2.1
                          have p100_3 := h100c.2.2.2
                          linarith only [hlam, p100_0]
                      · linarith only [h0, h11, h3, h6, h8, h9, h97, h99, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h11, h3, h6, h93, h94, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h11, h3, h6, h93, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h11, h93, h94, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h187 | h187
              · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                · linarith only [h10, h11, h188, h9, h93, hc35, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                  · linarith only [h190, h9, h93, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                      · rcases h0bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h193, h3, h6, h93, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h193, h6, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h193, h6, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h7, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h0, hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h193, h6, h9, h93, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h0, h193, h6, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h0, h7, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h1, hlam, p194_1]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h3, hlam, p194_1]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h193, h6, h9, h93, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h0, h3, h7, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi1]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h4, hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h6, hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h0, h3, h6, h7, h9, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1, u2ehi2]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h2, hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h5, hlam, p194_1]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h7, hlam, p194_0]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [h8, hlam, p194_1]
                        · have p194_0 := h194c.1
                          have p194_1 := h194c.2.1
                          have p194_2 := h194c.2.2.1
                          have p194_3 := h194c.2.2.2
                          linarith only [hlam, p194_0]
                      · linarith only [h11, h193, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h10, h187, h192, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                · linarith only [h11, h222, h9, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                  · linarith only [h224, h9, h93, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h226 | h226
                    · linarith only [h0, h10, h187, h226, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                      · linarith only [h11, h187, h228, h9, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h11, h228, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h0, h10, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
        · linarith only [h232, h9, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
          · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
            · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                      · rcases h0bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h232, h237, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1, u2ehi1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h1, h234, h240, hc01, hc45, hlam, hphi, ht0b, ht5b, p241_1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h232, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1, u2ehi1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          rcases p241_3 (m.d 0 1) (by simp) with h246 | h246
                          · rcases p241_3 (m.d 0 2) (by simp) with h247 | h247
                            · linarith only [h0, h247, hlam]
                            · linarith only [h247, h5, hlam]
                          · linarith only [h2, h246, hlam]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h0, hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h232, h237, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1, u2ehi1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h0, h232, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1, u2ehi1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          rcases p241_3 (m.d 0 1) (by simp) with h255 | h255
                          · rcases p241_3 (m.d 0 2) (by simp) with h256 | h256
                            · rcases p241_3 (m.d 0 3) (by simp) with h257 | h257
                              · linarith only [h257, h3, hlam]
                              · linarith only [h257, h7, hlam]
                            · linarith only [h256, h5, hlam]
                          · linarith only [h2, h255, hlam]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h1, hlam, p241_1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h3, hlam, p241_1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h232, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1, u2ehi1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          rcases p241_3 (m.d 0 1) (by simp) with h266 | h266
                          · rcases p241_3 (m.d 0 2) (by simp) with h267 | h267
                            · rcases p241_3 (m.d 0 3) (by simp) with h268 | h268
                              · rcases p241_3 (m.d 0 4) (by simp) with h269 | h269
                                · linarith only [h269, h6, hlam]
                                · linarith only [h269, h8, hlam]
                              · linarith only [h268, h7, hlam]
                            · linarith only [h267, h5, hlam]
                          · linarith only [h2, h266, hlam]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p241_1, u2ehi1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h4, hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h6, hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          rcases p241_3 (m.d 0 1) (by simp) with h279 | h279
                          · rcases p241_3 (m.d 0 2) (by simp) with h280 | h280
                            · rcases p241_3 (m.d 0 3) (by simp) with h281 | h281
                              · rcases p241_3 (m.d 0 4) (by simp) with h282 | h282
                                · rcases p241_3 (m.d 0 5) (by simp) with h283 | h283
                                  · linarith only [h283, h8, hlam]
                                  · rcases h3bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h0, h234, h240, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h0, h232, h237, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p285_1, u2ehi1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h0, h240, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      rcases p285_3 (m.d 0 3) (by simp) with h290 | h290
                                      · rcases p285_3 (m.d 1 3) (by simp) with h291 | h291
                                        · linarith only [h1, h291, hlam]
                                        · linarith only [h235, h291, hlam]
                                      · linarith only [h290, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h1, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h9, hlam, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h240, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h3, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h0, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h0, h240, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h0, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h6, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h234, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h237, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h234, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p285_1]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h7, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h235, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h238, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [h240, hlam, p285_0]
                                    · have p285_0 := h285c.1
                                      have p285_1 := h285c.2.1
                                      have p285_2 := h285c.2.2.1
                                      have p285_3 := h285c.2.2.2
                                      linarith only [hlam, p285_0]
                                · linarith only [h282, h8, hlam]
                              · linarith only [h281, h7, hlam]
                            · linarith only [h280, h5, hlam]
                          · linarith only [h2, h279, hlam]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h2, hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h5, hlam, p241_1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h7, hlam, p241_0]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [h8, hlam, p241_1]
                        · have p241_0 := h241c.1
                          have p241_1 := h241c.2.1
                          have p241_2 := h241c.2.2.1
                          have p241_3 := h241c.2.2.2
                          linarith only [hlam, p241_0]
                      · rcases h0bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h234, h236, h240, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h1, h234, h236, h240, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h232, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p324_1, u2ehi1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h329 | h329
                          · rcases p324_3 (m.d 0 2) (by simp) with h330 | h330
                            · linarith only [h0, h330, hlam]
                            · linarith only [h330, h5, hlam]
                          · linarith only [h2, h329, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h0, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h232, h237, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p324_1, u2ehi1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h0, h232, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p324_1, u2ehi1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h338 | h338
                          · rcases p324_3 (m.d 0 2) (by simp) with h339 | h339
                            · rcases p324_3 (m.d 0 3) (by simp) with h340 | h340
                              · linarith only [h3, h340, hlam]
                              · linarith only [h340, h7, hlam]
                            · linarith only [h339, h5, hlam]
                          · linarith only [h2, h338, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h1, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h3, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h232, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p324_1, u2ehi1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h349 | h349
                          · rcases p324_3 (m.d 0 2) (by simp) with h350 | h350
                            · rcases p324_3 (m.d 0 3) (by simp) with h351 | h351
                              · rcases p324_3 (m.d 0 4) (by simp) with h352 | h352
                                · linarith only [h352, h6, hlam]
                                · linarith only [h352, h8, hlam]
                              · linarith only [h351, h7, hlam]
                            · linarith only [h350, h5, hlam]
                          · linarith only [h2, h349, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p324_1, u2ehi1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h4, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h6, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h362 | h362
                          · rcases p324_3 (m.d 0 2) (by simp) with h363 | h363
                            · rcases p324_3 (m.d 0 3) (by simp) with h364 | h364
                              · rcases p324_3 (m.d 0 4) (by simp) with h365 | h365
                                · rcases p324_3 (m.d 0 5) (by simp) with h366 | h366
                                  · linarith only [h366, h8, hlam]
                                  · rcases h3bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h0, h234, h236, h240, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h0, h232, h237, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      rcases p368_3 (m.d 0 3) (by simp) with h372 | h372
                                      · rcases p368_3 (m.d 1 3) (by simp) with h373 | h373
                                        · linarith only [h1, h373, hlam]
                                        · linarith only [h234, h373, hlam]
                                      · linarith only [h372, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      rcases p368_3 (m.d 0 3) (by simp) with h377 | h377
                                      · rcases p368_3 (m.d 1 3) (by simp) with h378 | h378
                                        · linarith only [h1, h378, hlam]
                                        · linarith only [h235, h378, hlam]
                                      · linarith only [h377, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h1, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h9, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h1, h240, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h3, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h0, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h0, h240, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h6, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h234, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h237, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h240, hlam, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h7, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h235, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h238, hlam, p368_0]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [h0, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                                    · have p368_0 := h368c.1
                                      have p368_1 := h368c.2.1
                                      have p368_2 := h368c.2.2.1
                                      have p368_3 := h368c.2.2.2
                                      linarith only [hlam, p368_0]
                                · linarith only [h365, h8, hlam]
                              · linarith only [h364, h7, hlam]
                            · linarith only [h363, h5, hlam]
                          · linarith only [h2, h362, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h2, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h5, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h7, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h8, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                    · linarith only [h232, h234, h236, h239, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · linarith only [h238, h9, hc35, hlam, hphi, ht23, u2ehi1]
                · linarith only [h237, h9, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                · rcases m.htr 2 3 5 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h416 | h416
                    · linarith only [h232, h236, h414, h416, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h232, h416, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h235, h415, h9, hlam]
                · linarith only [h0, h3, h414, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h421 | h421
              · linarith only [h234, h235, h421, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h423 | h423
                · rcases m.htr 2 3 5 (by decide) (by decide) with h424 | h424
                  · linarith only [h0, h234, h235, h3, h424, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h424, h7, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h234, h423, h9, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
            · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
              · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                · linarith only [h0, h234, h3, h428, h430, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3, h430, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · linarith only [h234, h428, h429, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
              · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                · linarith only [h234, h435, h9, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h3, h435, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h438 | h438
                · linarith only [h234, h438, h9, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h3, h438, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
      · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
        · rcases m.htr 1 3 4 (by decide) (by decide) with h443 | h443
          · rcases m.htr 1 3 5 (by decide) (by decide) with h444 | h444
            · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
              · linarith only [h1, h4, h443, h445, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                    · linarith only [h4, h449, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                      · linarith only [h0, h4, h441, h447, h451, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases h0bigk with h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h0, h441, h448, h451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h456 | h456
                          · rcases p453_3 (m.d 0 2) (by simp) with h457 | h457
                            · linarith only [h0, h457, hlam]
                            · linarith only [h3, h457, hlam]
                          · linarith only [h1, h456, hlam]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h461 | h461
                          · rcases p453_3 (m.d 0 2) (by simp) with h462 | h462
                            · linarith only [h0, h462, hlam]
                            · linarith only [h4, h462, hlam]
                          · linarith only [h461, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h466 | h466
                          · rcases p453_3 (m.d 0 2) (by simp) with h467 | h467
                            · linarith only [h0, h467, hlam]
                            · linarith only [h467, h5, hlam]
                          · linarith only [h2, h466, hlam]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h0, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h473 | h473
                          · rcases p453_3 (m.d 0 2) (by simp) with h474 | h474
                            · rcases p453_3 (m.d 0 3) (by simp) with h475 | h475
                              · linarith only [h3, h475, hlam]
                              · rcases p453_3 (m.d 0 4) (by simp) with h477 | h477
                                · linarith only [h4, h477, hlam]
                                · rcases p453_3 (m.d 0 5) (by simp) with h479 | h479
                                  · linarith only [h479, h5, hlam]
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
                                      linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p453_1, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h448, h449, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p453_1, p481_1, u2ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1, p481_1]
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
                                      linarith only [h448, h449, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p481_1, u2ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h1, h451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h3, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h441, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h441, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h1, h441, h451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h6, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h443, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h447, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h451, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h7, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h444, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h448, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p453_1, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                            · linarith only [h3, h474, hlam]
                          · linarith only [h1, h473, hlam]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h509 | h509
                          · rcases p453_3 (m.d 0 2) (by simp) with h510 | h510
                            · rcases p453_3 (m.d 0 3) (by simp) with h511 | h511
                              · linarith only [h3, h511, hlam]
                              · linarith only [h511, h6, hlam]
                            · linarith only [h4, h510, hlam]
                          · linarith only [h0, h509, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h516 | h516
                          · rcases p453_3 (m.d 0 2) (by simp) with h517 | h517
                            · rcases p453_3 (m.d 0 3) (by simp) with h518 | h518
                              · linarith only [h3, h518, hlam]
                              · linarith only [h518, h7, hlam]
                            · linarith only [h5, h517, hlam]
                          · linarith only [h2, h516, hlam]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h1, hlam, p453_1]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h3, hlam, p453_1]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h526 | h526
                          · rcases p453_3 (m.d 0 2) (by simp) with h527 | h527
                            · rcases p453_3 (m.d 0 3) (by simp) with h528 | h528
                              · rcases p453_3 (m.d 0 4) (by simp) with h529 | h529
                                · linarith only [h529, h6, hlam]
                                · rcases p453_3 (m.d 0 5) (by simp) with h531 | h531
                                  · linarith only [h531, h7, hlam]
                                  · linarith only [h531, h8, hlam]
                              · linarith only [h528, h6, hlam]
                            · linarith only [h4, h527, hlam]
                          · linarith only [h0, h441, h448, h449, h526, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi3]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          rcases p453_3 (m.d 0 1) (by simp) with h537 | h537
                          · rcases p453_3 (m.d 0 2) (by simp) with h538 | h538
                            · rcases p453_3 (m.d 0 3) (by simp) with h539 | h539
                              · rcases p453_3 (m.d 0 4) (by simp) with h540 | h540
                                · linarith only [h540, h6, hlam]
                                · rcases p453_3 (m.d 0 5) (by simp) with h542 | h542
                                  · linarith only [h542, h7, hlam]
                                  · rcases h3bigk with h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h3, h442, h444, h445, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p544_1, u2ehi3]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h3, h448, h449, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p544_1, u2ehi3]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      rcases p544_3 (m.d 0 3) (by simp) with h548 | h548
                                      · rcases p544_3 (m.d 1 3) (by simp) with h549 | h549
                                        · linarith only [h1, h549, hlam]
                                        · linarith only [h443, h549, hlam]
                                      · linarith only [h548, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      rcases p544_3 (m.d 0 3) (by simp) with h553 | h553
                                      · rcases p544_3 (m.d 1 3) (by simp) with h554 | h554
                                        · linarith only [h1, h554, hlam]
                                        · linarith only [h444, h554, hlam]
                                      · linarith only [h553, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h1, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h448, h449, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p544_1, u2ehi3]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h441, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h441, h451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h3, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h441, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h441, h451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h6, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h443, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h447, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h451, hlam, p544_1]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h7, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h444, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h448, hlam, p544_0]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [h0, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1]
                                    · have p544_0 := h544c.1
                                      have p544_1 := h544c.2.1
                                      have p544_2 := h544c.2.2.1
                                      have p544_3 := h544c.2.2.2
                                      linarith only [hlam, p544_0]
                              · linarith only [h539, h7, hlam]
                            · linarith only [h5, h538, hlam]
                          · linarith only [h2, h537, hlam]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi1]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h4, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h6, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h8, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h2, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h5, hlam, p453_1]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h7, hlam, p453_0]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [h4, h8, hc45, hlam, hphi, ht23, ht34, p453_1, u2ehi3]
                        · have p453_0 := h453c.1
                          have p453_1 := h453c.2.1
                          have p453_2 := h453c.2.2.1
                          have p453_3 := h453c.2.2.2
                          linarith only [hlam, p453_0]
                  · linarith only [h0, h441, h444, h448, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h447, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
              · linarith only [h0, h442, h443, h444, h593, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                · rcases m.htr 2 3 5 (by decide) (by decide) with h596 | h596
                  · linarith only [h442, h443, h444, h596, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h598 | h598
                    · linarith only [h442, h443, h444, h598, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h600 | h600
                      · linarith only [h442, h443, h444, h600, h7, h8, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h3, h595, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p602_1]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h442, h443, h444, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          rcases p602_3 (m.d 0 1) (by simp) with h606 | h606
                          · rcases p602_3 (m.d 0 2) (by simp) with h607 | h607
                            · linarith only [h0, h607, hlam]
                            · linarith only [h4, h607, hlam]
                          · linarith only [h606, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h442, h443, h444, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h0, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h442, h443, h444, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          rcases p602_3 (m.d 0 1) (by simp) with h615 | h615
                          · rcases p602_3 (m.d 0 2) (by simp) with h616 | h616
                            · rcases p602_3 (m.d 0 3) (by simp) with h617 | h617
                              · linarith only [h3, h617, hlam]
                              · linarith only [h6, h617, hlam]
                            · linarith only [h4, h616, hlam]
                          · linarith only [h0, h615, hlam, p602_1]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h0, h442, h443, h444, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h1, hlam, p602_1]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h3, hlam, p602_1]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          rcases p602_3 (m.d 0 1) (by simp) with h626 | h626
                          · rcases p602_3 (m.d 0 2) (by simp) with h627 | h627
                            · rcases p602_3 (m.d 0 3) (by simp) with h628 | h628
                              · rcases p602_3 (m.d 0 4) (by simp) with h629 | h629
                                · linarith only [h6, h629, hlam]
                                · rcases p602_3 (m.d 0 5) (by simp) with h631 | h631
                                  · linarith only [h631, h7, hlam]
                                  · linarith only [h631, h8, hlam]
                              · linarith only [h6, h628, hlam]
                            · linarith only [h4, h627, hlam]
                          · linarith only [h0, h626, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi1]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h0, h3, h442, h443, h444, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h0, h441, h595, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h4, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h6, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h8, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h2, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h5, hlam, p602_1]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h7, hlam, p602_0]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [h4, h8, hc45, hlam, hphi, ht23, ht34, p602_1, u2ehi3]
                        · have p602_0 := h602c.1
                          have p602_1 := h602c.2.1
                          have p602_2 := h602c.2.2.1
                          have p602_3 := h602c.2.2.2
                          linarith only [hlam, p602_0]
                · linarith only [h595, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h441, h443, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h441, h442, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
        · linarith only [h441, h651, hc23, hlam, hphi, u2ehi3]
        · linarith only [h4, h651, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h654 | h654
    · linarith only [h6, h654, h7, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
      · rcases m.htr 1 2 4 (by decide) (by decide) with h657 | h657
        · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
          · rcases m.htr 1 3 5 (by decide) (by decide) with h659 | h659
            · linarith only [h1, h659, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
              · linarith only [h1, h4, h654, h658, h661, h7, hc35, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h663 | h663
                · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
                  · linarith only [h0, h656, h664, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                    · linarith only [h4, h654, h666, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                      · linarith only [h4, h654, h668, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h3, h663, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p670_1, u2ehi3]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h673 | h673
                          · rcases p670_3 (m.d 0 2) (by simp) with h674 | h674
                            · linarith only [h0, h674, hlam]
                            · linarith only [h3, h674, hlam]
                          · linarith only [h1, h673, hlam]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h678 | h678
                          · rcases p670_3 (m.d 0 2) (by simp) with h679 | h679
                            · linarith only [h0, h679, hlam]
                            · linarith only [h4, h679, hlam]
                          · linarith only [h678, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h683 | h683
                          · rcases p670_3 (m.d 0 2) (by simp) with h684 | h684
                            · linarith only [h0, h684, hlam]
                            · linarith only [h5, h684, hlam]
                          · linarith only [h2, h683, hlam]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h690 | h690
                          · rcases p670_3 (m.d 0 2) (by simp) with h691 | h691
                            · rcases p670_3 (m.d 0 3) (by simp) with h692 | h692
                              · linarith only [h3, h692, hlam]
                              · rcases p670_3 (m.d 0 4) (by simp) with h694 | h694
                                · linarith only [h4, h694, hlam]
                                · rcases p670_3 (m.d 0 5) (by simp) with h696 | h696
                                  · linarith only [h5, h696, hlam]
                                  · linarith only [h696, h7, hlam]
                            · linarith only [h3, h691, hlam]
                          · linarith only [h1, h690, hlam]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h701 | h701
                          · rcases p670_3 (m.d 0 2) (by simp) with h702 | h702
                            · rcases p670_3 (m.d 0 3) (by simp) with h703 | h703
                              · linarith only [h3, h703, hlam]
                              · linarith only [h6, h703, hlam]
                            · linarith only [h4, h702, hlam]
                          · linarith only [h0, h701, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          rcases p670_3 (m.d 0 1) (by simp) with h708 | h708
                          · rcases p670_3 (m.d 0 2) (by simp) with h709 | h709
                            · rcases p670_3 (m.d 0 3) (by simp) with h710 | h710
                              · linarith only [h3, h710, hlam]
                              · rcases p670_3 (m.d 0 4) (by simp) with h712 | h712
                                · linarith only [h4, h712, hlam]
                                · rcases p670_3 (m.d 0 5) (by simp) with h714 | h714
                                  · linarith only [h5, h714, hlam]
                                  · rcases h3bigk with h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h0, h657, h658, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p670_1, p716_1, u2ehi3]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h0, h663, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p670_1, p716_1, u2ehi3]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h0, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p670_1, p716_1]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h7, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h1, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h663, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p716_1, u2ehi3]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h0, h1, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p670_1, p716_1]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h659, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h3, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h656, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h656, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p716_1]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h664, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h6, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h658, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h663, hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [hlam, p716_0]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h668, hlam, p716_1]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [hc03, hc35, hlam, hphi, p716_1]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h657, h658, h668, hc45, hlam, hphi, ht23, ht34, p716_1, u2ehi3]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h663, h668, hc45, hlam, hphi, ht23, ht34, p716_1, u2ehi3]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [h668, hc34, hc45, hlam, hphi, p716_1]
                                    · have p716_0 := h716c.1
                                      have p716_1 := h716c.2.1
                                      have p716_2 := h716c.2.2.1
                                      have p716_3 := h716c.2.2.2
                                      linarith only [hlam, p716_0]
                            · linarith only [h5, h709, hlam]
                          · linarith only [h2, h708, hlam]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h1, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h3, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h4, h668, h7, hc45, hlam, hphi, ht23, ht34, p670_1, u2ehi3]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h7, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p670_1, u2ehi1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h4, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h6, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h654, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h2, hlam, p670_0]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h5, hlam, p670_1]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h3, h663, h668, h7, hc45, hlam, hphi, ht23, ht34, p670_1, u2ehi3]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [h4, h668, h7, hc45, hlam, hphi, ht23, ht34, p670_1, u2ehi3]
                        · have p670_0 := h670c.1
                          have p670_1 := h670c.2.1
                          have p670_2 := h670c.2.2.1
                          have p670_3 := h670c.2.2.2
                          linarith only [hlam, p670_0]
                · linarith only [h6, h663, h7, hc35, hlam, hphi, ht23, u2ehi2]
          · linarith only [h6, h658, h7, hc13, hc35, hlam, hphi]
        · linarith only [h656, h657, hc24, hlam, hphi, u2ehi2]
      · linarith only [h3, h656, h7, hc35, hlam, hphi, ht23, u2ehi1]

end R2N4
