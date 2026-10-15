import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h12, h14, h17, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h13, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h14, h24, h26, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h10, h14, h28, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h25, h26, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, h14, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, h14, h6, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h10, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h10, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h1, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h3, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h10, h14, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h10, h14, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h4, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h6, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h0, h10, h14, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h2, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h5, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h7, hlam, p30_0]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [h8, hlam, p30_1]
                        · have p30_0 := h30c.1
                          have p30_1 := h30c.2.1
                          have p30_2 := h30c.2.2.1
                          have p30_3 := h30c.2.2.2
                          linarith only [hlam, p30_0]
                  · linarith only [h0, h13, h24, h25, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h12, h24, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
              · linarith only [h12, h13, h58, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                  · linarith only [h13, h61, h9, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h10, h58, h63, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h10, h13, h58, h60, h65, h7, h9, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases h0bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h13, h3, h6, h65, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h13, h6, h65, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi2]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h10, h12, h13, h65, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h10, h12, h13, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h0, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h10, h12, h13, h6, h65, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h0, h10, h12, h13, h65, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h0, h10, h12, h13, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h1, hlam, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h3, hlam, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h10, h12, h13, h65, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h0, h10, h12, h13, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h4, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h6, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h0, h10, h12, h13, h3, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi3]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h2, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h5, hlam, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h7, hlam, p67_0]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [h8, hlam, p67_1]
                        · have p67_0 := h67c.1
                          have p67_1 := h67c.2.1
                          have p67_2 := h67c.2.2.1
                          have p67_3 := h67c.2.2.2
                          linarith only [hlam, p67_0]
                · linarith only [h12, h13, h60, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
            · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
              · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                · linarith only [h0, h12, h3, h94, h96, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                      · rcases h0bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h0, h10, h96, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h11, h12, h6, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h11, h12, h6, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          rcases p101_3 (m.d 0 1) (by simp) with h106 | h106
                          · rcases p101_3 (m.d 0 2) (by simp) with h107 | h107
                            · linarith only [h0, h107, hlam]
                            · linarith only [h107, h5, hlam]
                          · linarith only [h106, h2, hlam]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h0, hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h11, h12, h6, h94, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h0, h11, h12, h6, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          rcases p101_3 (m.d 0 1) (by simp) with h115 | h115
                          · rcases p101_3 (m.d 0 2) (by simp) with h116 | h116
                            · rcases p101_3 (m.d 0 3) (by simp) with h117 | h117
                              · linarith only [h117, h3, hlam]
                              · linarith only [h117, h7, hlam]
                            · linarith only [h116, h5, hlam]
                          · linarith only [h115, h2, hlam]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h1, hlam, p101_1]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h3, hlam, p101_1]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h11, h12, h6, h94, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          rcases p101_3 (m.d 0 1) (by simp) with h126 | h126
                          · rcases p101_3 (m.d 0 2) (by simp) with h127 | h127
                            · rcases p101_3 (m.d 0 3) (by simp) with h128 | h128
                              · rcases p101_3 (m.d 0 4) (by simp) with h129 | h129
                                · linarith only [h129, h6, hlam]
                                · linarith only [h129, h8, hlam]
                              · linarith only [h128, h7, hlam]
                            · linarith only [h127, h5, hlam]
                          · linarith only [h126, h2, hlam]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h0, h10, h96, h98, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h4, hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h6, hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          rcases p101_3 (m.d 0 1) (by simp) with h139 | h139
                          · rcases p101_3 (m.d 0 2) (by simp) with h140 | h140
                            · rcases p101_3 (m.d 0 3) (by simp) with h141 | h141
                              · rcases p101_3 (m.d 0 4) (by simp) with h142 | h142
                                · rcases p101_3 (m.d 0 5) (by simp) with h143 | h143
                                  · linarith only [h143, h8, hlam]
                                  · rcases h0emax with h145 | h145 | h145 | h145 | h145
                                    · linarith only [h0, h11, h145, h2, h3, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                                    · linarith only [h11, h145, h2, h3, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                                    · linarith only [h11, h145, h2, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                                    · linarith only [h11, h145, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi4]
                                    · rcases h5bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h11, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, p150_1, u2ehi4]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, p150_1, u2ehi4]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h3, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p101_1, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p101_1, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h2, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h94, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p150_1, u2ehi4]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h100, h2, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p101_1, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h2, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p101_1, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h5, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h11, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h10, h100, h96, h98, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h11, h2, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p101_1, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h7, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h94, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h98, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h3, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h8, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h95, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h99, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h100, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                · linarith only [h142, h8, hlam]
                              · linarith only [h141, h7, hlam]
                            · linarith only [h140, h5, hlam]
                          · linarith only [h139, h2, hlam]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h2, hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h5, hlam, p101_1]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h7, hlam, p101_0]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [h8, hlam, p101_1]
                        · have p101_0 := h101c.1
                          have p101_1 := h101c.2.1
                          have p101_2 := h101c.2.2.1
                          have p101_3 := h101c.2.2.2
                          linarith only [hlam, p101_0]
                      · linarith only [h100, h12, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h12, h3, h6, h94, h95, h99, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h12, h3, h6, h94, h98, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h12, h94, h95, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
              · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                · linarith only [h12, h190, h9, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                  · linarith only [h192, h9, h94, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h195 | h195
                      · rcases h0bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h195, h6, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h195, h6, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h7, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h195, h6, h9, h94, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h195, h6, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h7, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h1, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h3, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h195, h6, h9, h94, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h3, h7, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h4, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h6, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h0, h3, h6, h7, h9, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p196_1, u2ehi2]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h2, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h5, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h7, hlam, p196_0]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [h8, hlam, p196_1]
                        · have p196_0 := h196c.1
                          have p196_1 := h196c.2.1
                          have p196_2 := h196c.2.2.1
                          have p196_3 := h196c.2.2.2
                          linarith only [hlam, p196_0]
                      · linarith only [h0, h10, h194, h195, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h12, h189, h194, hc34, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                · linarith only [h12, h224, h9, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                  · linarith only [h226, h9, h94, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                    · linarith only [h10, h189, h228, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h230 | h230
                      · linarith only [h10, h189, h230, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h12, h230, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
        · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
      · linarith only [h235, h9, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
        · linarith only [h0, h237, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
          · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
            · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                      · rcases h0bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi2]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h1, h239, h245, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h237, h244, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h237, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h0, hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h237, h244, h4, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h0, h237, h244, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h0, h237, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h1, hlam, p246_1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h3, hlam, p246_1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h237, h244, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h0, h237, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h4, hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h6, hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h0, h237, h3, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1, u2ehi1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h2, hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h5, hlam, p246_1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h7, hlam, p246_0]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [h8, hlam, p246_1]
                        · have p246_0 := h246c.1
                          have p246_1 := h246c.2.1
                          have p246_2 := h246c.2.2.1
                          have p246_3 := h246c.2.2.2
                          linarith only [hlam, p246_0]
                      · rcases h0bigk with h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi2]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h237, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h237, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h237, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h0, hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h237, h5, h6, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h0, h237, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h0, h237, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h1, hlam, p272_1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h3, hlam, p272_1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h237, h5, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h0, h237, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h4, hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h6, hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h237, h5, h6, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h2, hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h5, hlam, p272_1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h7, hlam, p272_0]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [h8, hlam, p272_1]
                        · have p272_0 := h272c.1
                          have p272_1 := h272c.2.1
                          have p272_2 := h272c.2.2.1
                          have p272_3 := h272c.2.2.2
                          linarith only [hlam, p272_0]
                    · linarith only [h1, h239, h241, h244, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h243, h3, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h0, h242, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                    · linarith only [h0, h235, h241, h3, h301, h303, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h235, h303, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h1, h240, h302, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h3, h301, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
              · linarith only [h239, h240, h308, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                  · linarith only [h0, h239, h240, h3, h311, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h311, h7, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h310, h9, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
            · rcases m.htr 1 4 5 (by decide) (by decide) with h316 | h316
              · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                · linarith only [h0, h239, h3, h315, h317, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3, h317, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · linarith only [h239, h315, h316, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
              · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                · linarith only [h0, h239, h3, h322, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h0, h3, h322, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                · linarith only [h239, h325, h9, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h3, h325, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
    · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
      · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
        · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
          · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
            · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
              · linarith only [h1, h331, h333, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                    · linarith only [h337, h4, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h339 | h339
                      · linarith only [h0, h328, h335, h339, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h0, h328, h336, h337, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, u2ehi3]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h344 | h344
                          · rcases p341_3 (m.d 0 2) (by simp) with h345 | h345
                            · linarith only [h0, h345, hlam]
                            · linarith only [h3, h345, hlam]
                          · linarith only [h1, h344, hlam]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h349 | h349
                          · rcases p341_3 (m.d 0 2) (by simp) with h350 | h350
                            · linarith only [h0, h350, hlam]
                            · linarith only [h350, h4, hlam]
                          · linarith only [h349, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h354 | h354
                          · rcases p341_3 (m.d 0 2) (by simp) with h355 | h355
                            · linarith only [h0, h355, hlam]
                            · linarith only [h355, h5, hlam]
                          · linarith only [h2, h354, hlam]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h0, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h361 | h361
                          · rcases p341_3 (m.d 0 2) (by simp) with h362 | h362
                            · rcases p341_3 (m.d 0 3) (by simp) with h363 | h363
                              · linarith only [h3, h363, hlam]
                              · rcases p341_3 (m.d 0 4) (by simp) with h365 | h365
                                · linarith only [h365, h4, hlam]
                                · rcases p341_3 (m.d 0 5) (by simp) with h367 | h367
                                  · linarith only [h367, h5, hlam]
                                  · rcases h0emax with h369 | h369 | h369 | h369 | h369
                                    · linarith only [h0, h369, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p341_1]
                                    · linarith only [h1, h328, h336, h337, h369, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, u2ehi3]
                                    · rcases h5bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h0, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p341_1, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h0, h337, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, p372_1, u2ehi3]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h0, h339, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h8, hlam, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h2, hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h337, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p372_1, u2ehi3]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h0, h2, h339, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h333, hlam, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h5, hlam, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h330, hlam, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h328, h336, h339, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h337, hlam, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h7, hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h332, hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h336, hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [hlam, p372_0]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h339, hlam, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h5, hc45, hlam, hphi, ht23, ht34, p372_1, u2ehi4]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h330, hc45, hlam, hphi, ht23, ht34, p372_1, u2ehi4]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p372_1, u2ehi4]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [h339, hc34, hc45, hlam, hphi, p372_1]
                                      · have p372_0 := h372c.1
                                        have p372_1 := h372c.2.1
                                        have p372_2 := h372c.2.2.1
                                        have p372_3 := h372c.2.2.2
                                        linarith only [hlam, p372_0]
                                    · rcases h5bigk with h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h329, h333, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p398_1, u2ehi3]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h0, h337, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p398_1, u2ehi3]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h0, h339, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h8, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h2, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h337, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p398_1, u2ehi3]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h0, h2, h339, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h333, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h5, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h330, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h0, h339, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h337, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h7, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h332, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h336, hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h339, hlam, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h5, hc45, hlam, hphi, ht23, ht34, p398_1, u2ehi4]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h330, hc45, hlam, hphi, ht23, ht34, p398_1, u2ehi4]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p398_1, u2ehi4]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [h339, hc34, hc45, hlam, hphi, p398_1]
                                      · have p398_0 := h398c.1
                                        have p398_1 := h398c.2.1
                                        have p398_2 := h398c.2.2.1
                                        have p398_3 := h398c.2.2.2
                                        linarith only [hlam, p398_0]
                                    · rcases h5bigk with h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c | h424c
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h329, h333, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p424_1, u2ehi3]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h0, h337, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p424_1, u2ehi3]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h0, h339, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h8, hlam, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h2, hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h337, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p424_1, u2ehi3]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h0, h2, h339, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h333, hlam, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h5, hlam, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h330, hlam, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h0, h339, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h337, hlam, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h7, hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h332, hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h336, hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [hlam, p424_0]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h339, hlam, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h5, hc45, hlam, hphi, ht23, ht34, p424_1, u2ehi4]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h330, hc45, hlam, hphi, ht23, ht34, p424_1, u2ehi4]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p424_1, u2ehi4]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [h339, hc34, hc45, hlam, hphi, p424_1]
                                      · have p424_0 := h424c.1
                                        have p424_1 := h424c.2.1
                                        have p424_2 := h424c.2.2.1
                                        have p424_3 := h424c.2.2.2
                                        linarith only [hlam, p424_0]
                            · linarith only [h3, h362, hlam]
                          · linarith only [h1, h361, hlam]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h452 | h452
                          · rcases p341_3 (m.d 0 2) (by simp) with h453 | h453
                            · rcases p341_3 (m.d 0 3) (by simp) with h454 | h454
                              · linarith only [h3, h454, hlam]
                              · linarith only [h454, h6, hlam]
                            · linarith only [h4, h453, hlam]
                          · linarith only [h0, h452, hlam, p341_1]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h459 | h459
                          · rcases p341_3 (m.d 0 2) (by simp) with h460 | h460
                            · rcases p341_3 (m.d 0 3) (by simp) with h461 | h461
                              · linarith only [h3, h461, hlam]
                              · linarith only [h461, h7, hlam]
                            · linarith only [h460, h5, hlam]
                          · linarith only [h2, h459, hlam]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h1, hlam, p341_1]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h3, hlam, p341_1]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h469 | h469
                          · rcases p341_3 (m.d 0 2) (by simp) with h470 | h470
                            · rcases p341_3 (m.d 0 3) (by simp) with h471 | h471
                              · rcases p341_3 (m.d 0 4) (by simp) with h472 | h472
                                · linarith only [h472, h6, hlam]
                                · rcases p341_3 (m.d 0 5) (by simp) with h474 | h474
                                  · linarith only [h474, h7, hlam]
                                  · linarith only [h474, h8, hlam]
                              · linarith only [h471, h6, hlam]
                            · linarith only [h4, h470, hlam]
                          · linarith only [h0, h469, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, u2ehi1]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          rcases p341_3 (m.d 0 1) (by simp) with h480 | h480
                          · rcases p341_3 (m.d 0 2) (by simp) with h481 | h481
                            · rcases p341_3 (m.d 0 3) (by simp) with h482 | h482
                              · rcases p341_3 (m.d 0 4) (by simp) with h483 | h483
                                · linarith only [h483, h6, hlam]
                                · rcases p341_3 (m.d 0 5) (by simp) with h485 | h485
                                  · linarith only [h485, h7, hlam]
                                  · rcases h0emax with h487 | h487 | h487 | h487 | h487
                                    · linarith only [h0, h328, h336, h337, h487, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · linarith only [h2, h3, h329, h333, h487, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, u2ehi3]
                                    · linarith only [h2, h329, h333, h487, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, u2ehi3]
                                    · rcases h5bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h3, h329, h333, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, p491_1, u2ehi3]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h3, h337, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, p491_1, u2ehi3]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h3, h339, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h8, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h2, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h337, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p491_1, u2ehi3]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h2, h3, h339, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h333, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h5, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h330, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h328, h336, h339, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h337, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h7, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h332, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h336, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h339, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h8, hc04, hc45, hlam, hphi, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h330, hc45, hlam, hphi, ht23, ht34, p491_1, u2ehi4]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p491_1, u2ehi4]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h339, hc34, hc45, hlam, hphi, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                    · rcases h5bigk with h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c | h517c
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h329, h333, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p517_1, u2ehi3]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h337, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p517_1, u2ehi3]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h3, h339, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h8, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h2, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h337, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p517_1, u2ehi3]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h2, h3, h339, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p341_1, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h333, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h5, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h330, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h0, h339, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h337, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h7, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h332, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h336, hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h339, hlam, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h5, hc45, hlam, hphi, ht23, ht34, p517_1, u2ehi4]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h330, hc45, hlam, hphi, ht23, ht34, p517_1, u2ehi4]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p517_1, u2ehi4]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [h339, hc34, hc45, hlam, hphi, p517_1]
                                      · have p517_0 := h517c.1
                                        have p517_1 := h517c.2.1
                                        have p517_2 := h517c.2.2.1
                                        have p517_3 := h517c.2.2.2
                                        linarith only [hlam, p517_0]
                              · linarith only [h482, h7, hlam]
                            · linarith only [h481, h5, hlam]
                          · linarith only [h2, h480, hlam]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p341_1, u2ehi1]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h4, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h6, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h8, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h2, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h5, hlam, p341_1]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h7, hlam, p341_0]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [h4, h8, hc45, hlam, hphi, ht23, ht34, p341_1, u2ehi3]
                        · have p341_0 := h341c.1
                          have p341_1 := h341c.2.1
                          have p341_2 := h341c.2.2.1
                          have p341_3 := h341c.2.2.2
                          linarith only [hlam, p341_0]
                  · linarith only [h0, h328, h332, h336, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h335, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h558 | h558
              · linarith only [h0, h329, h331, h332, h558, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
                · rcases m.htr 2 3 5 (by decide) (by decide) with h561 | h561
                  · linarith only [h329, h331, h332, h561, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                    · linarith only [h329, h331, h332, h563, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h565 | h565
                      · linarith only [h329, h331, h332, h565, h7, h8, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h3, h560, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h329, h331, h332, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          rcases p567_3 (m.d 0 1) (by simp) with h571 | h571
                          · rcases p567_3 (m.d 0 2) (by simp) with h572 | h572
                            · linarith only [h0, h572, hlam]
                            · linarith only [h4, h572, hlam]
                          · linarith only [h571, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h329, h331, h332, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h329, h331, h332, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          rcases p567_3 (m.d 0 1) (by simp) with h580 | h580
                          · rcases p567_3 (m.d 0 2) (by simp) with h581 | h581
                            · rcases p567_3 (m.d 0 3) (by simp) with h582 | h582
                              · linarith only [h3, h582, hlam]
                              · linarith only [h582, h6, hlam]
                            · linarith only [h4, h581, hlam]
                          · linarith only [h0, h580, hlam, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, h329, h331, h332, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h1, hlam, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h3, hlam, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          rcases p567_3 (m.d 0 1) (by simp) with h591 | h591
                          · rcases p567_3 (m.d 0 2) (by simp) with h592 | h592
                            · rcases p567_3 (m.d 0 3) (by simp) with h593 | h593
                              · rcases p567_3 (m.d 0 4) (by simp) with h594 | h594
                                · linarith only [h594, h6, hlam]
                                · rcases p567_3 (m.d 0 5) (by simp) with h596 | h596
                                  · linarith only [h596, h7, hlam]
                                  · linarith only [h596, h8, hlam]
                              · linarith only [h593, h6, hlam]
                            · linarith only [h4, h592, hlam]
                          · linarith only [h0, h591, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, h3, h329, h331, h332, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, h330, h560, h561, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h4, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h6, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h8, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h2, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h5, hlam, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h7, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h4, h8, hc45, hlam, hphi, ht23, ht34, p567_1, u2ehi3]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                · linarith only [h560, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h328, h331, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h0, h328, h330, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · linarith only [h328, h329, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h617 | h617
      · linarith only [h328, h617, hc23, hlam, hphi, u2ehi3]
      · linarith only [h4, h617, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]

end R2N4
