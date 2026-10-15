import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
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
                        linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h13, hc01, hc35, hlam, hphi, ht0b, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        rcases p20_3 (m.d 0 2) (by simp) with h24 | h24
                        · rcases p20_3 (m.d 1 2) (by simp) with h25 | h25
                          · linarith only [h0, h25, hlam]
                          · linarith only [h25, h8, hlam]
                        · linarith only [h24, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        rcases p20_3 (m.d 0 2) (by simp) with h29 | h29
                        · rcases p20_3 (m.d 1 2) (by simp) with h30 | h30
                          · linarith only [h0, h30, hlam]
                          · linarith only [h30, h9, hlam]
                        · linarith only [h29, hlam, p20_0]
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
                        linarith only [h13, h18, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p20_1]
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
                        linarith only [h0, h12, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
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
                        linarith only [h12, hc34, hlam, hphi, ht45, p20_1, u5elo2]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [hlam, p20_0]
                · linarith only [h0, h11, h12, h13, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h10, h12, h55, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                    · rcases h2bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h10, h55, h58, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        rcases p59_3 (m.d 0 2) (by simp) with h62 | h62
                        · rcases p59_3 (m.d 1 2) (by simp) with h63 | h63
                          · linarith only [h0, h63, hlam]
                          · linarith only [h63, h7, hlam]
                        · linarith only [h62, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h57, hc01, hc45, hlam, hphi, ht0b, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        rcases p59_3 (m.d 0 2) (by simp) with h68 | h68
                        · rcases p59_3 (m.d 1 2) (by simp) with h69 | h69
                          · linarith only [h0, h69, hlam]
                          · linarith only [h69, h9, hlam]
                        · linarith only [h68, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, hlam, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h57, hc01, hc45, hlam, hphi, ht0b, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h2, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h7, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h12, hlam, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h55, hlam, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h3, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h8, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h10, h12, h55, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h4, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h9, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hc23, hlam, hphi, ht34, ht45, p59_1, u5elo2]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h57, hlam, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                    · linarith only [h12, h58, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                    · linarith only [h0, h10, h57, h7, h94, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h12, h94, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h10, h11, h6, hc34, hlam, hphi, ht45, u5elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
            · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
              · linarith only [h0, h10, h2, h98, h99, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                    · rcases h2bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, h101, h103, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, h101, h103, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, h101, h103, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        rcases p104_3 (m.d 0 2) (by simp) with h109 | h109
                        · rcases p104_3 (m.d 1 2) (by simp) with h110 | h110
                          · linarith only [h0, h110, hlam]
                          · linarith only [h110, h9, hlam]
                        · linarith only [h109, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, hlam, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h101, h103, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, h101, h103, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h2, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h7, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h99, hlam, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h10, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h3, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h8, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h0, h101, h103, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h4, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h9, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h101, hlam, p104_0]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [h102, hlam, p104_1]
                      · have p104_0 := h104c.1
                        have p104_1 := h104c.2.1
                        have p104_2 := h104c.2.2.1
                        have p104_3 := h104c.2.2.2
                        linarith only [hlam, p104_0]
                    · linarith only [h10, h103, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h101, h102, h99, hc35, hlam, hphi, u5elo4]
                · linarith only [h10, h101, h98, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
              · linarith only [h137, h6, h7, h98, hc34, hlam, hphi, ht45, u5elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                · linarith only [h139, h7, h98, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
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
                        linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
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
                        linarith only [h0, h141, hc01, hc45, hlam, hphi, ht0b, ht5b, p143_1]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        rcases p143_3 (m.d 0 2) (by simp) with h152 | h152
                        · rcases p143_3 (m.d 1 2) (by simp) with h153 | h153
                          · linarith only [h0, h153, hlam]
                          · linarith only [h153, h9, hlam]
                        · linarith only [h152, hlam, p143_0]
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
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [h0, h141, hc01, hc45, hlam, hphi, ht0b, ht5b, p143_1]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [h0, h139, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
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
                        linarith only [h137, hlam, p143_1]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [h139, hlam, p143_1]
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
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [hlam, p143_0]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [h0, h139, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
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
                        linarith only [hc23, hlam, hphi, ht34, ht45, p143_1, u5elo2]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [h141, hlam, p143_1]
                      · have p143_0 := h143c.1
                        have p143_1 := h143c.2.1
                        have p143_2 := h143c.2.2.1
                        have p143_3 := h143c.2.2.2
                        linarith only [hlam, p143_0]
                    · linarith only [h10, h142, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h178 | h178
                    · rcases h2bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        rcases p179_3 (m.d 0 2) (by simp) with h182 | h182
                        · rcases p179_3 (m.d 1 2) (by simp) with h183 | h183
                          · linarith only [h0, h183, hlam]
                          · linarith only [h183, h7, hlam]
                        · linarith only [h182, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        rcases p179_3 (m.d 0 2) (by simp) with h187 | h187
                        · rcases p179_3 (m.d 1 2) (by simp) with h188 | h188
                          · linarith only [h0, h188, hlam]
                          · linarith only [h188, h8, hlam]
                        · linarith only [h187, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        rcases p179_3 (m.d 0 2) (by simp) with h192 | h192
                        · rcases p179_3 (m.d 1 2) (by simp) with h193 | h193
                          · linarith only [h0, h193, hlam]
                          · linarith only [h193, h9, hlam]
                        · linarith only [h192, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h141, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h2, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h7, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h137, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h139, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h3, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h8, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h141, hc23, hlam, hphi, ht34, ht45, p179_1, u5elo2]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h141, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h4, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h9, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h6, h9, h98, hc23, hlam, hphi, ht34, ht45, p179_1, u5elo0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h6, h9, h98, hc24, hlam, hphi, ht45, p179_1, u5elo0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                    · linarith only [h10, h178, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h4, h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
        · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
          · linarith only [h220, h7, h8, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h222 | h222
            · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
              · linarith only [h220, h223, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                · linarith only [h0, h2, h223, h225, h5, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2, h222, h223, h225, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
              · linarith only [h0, h228, h3, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                · linarith only [h0, h2, h222, h228, h230, h5, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
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
                        linarith only [h0, h219, hc01, hc25, hlam, hphi, ht0b, ht5b, p234_1]
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
                        linarith only [h0, h219, h230, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        rcases p234_3 (m.d 0 2) (by simp) with h243 | h243
                        · rcases p234_3 (m.d 1 2) (by simp) with h244 | h244
                          · linarith only [h0, h244, hlam]
                          · linarith only [h219, h244, hlam]
                        · linarith only [h243, hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h0, hlam, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h8, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h8, hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h0, h230, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p234_1]
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
                        linarith only [h228, hlam, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h230, hlam, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h3, hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h0, h2, h228, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h0, h2, h228, h230, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h4, hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h219, hlam, p234_0]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h219, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [h232, hlam, p234_1]
                      · have p234_0 := h234c.1
                        have p234_1 := h234c.2.1
                        have p234_2 := h234c.2.2.1
                        have p234_3 := h234c.2.2.2
                        linarith only [hlam, p234_0]
                    · linarith only [h219, h228, h233, h8, hc25, hlam, hphi, u5elo4]
                  · linarith only [h219, h230, h232, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h219, h4, h7, hc23, hlam, hphi, ht34, ht45, u5elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
      · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
        · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
          · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
            · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
              · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h2, h271, h277, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                    · linarith only [h275, h277, h279, hlam]
                    · rcases h2bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, h272, h277, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, h272, h275, h277, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        rcases p281_3 (m.d 0 2) (by simp) with h285 | h285
                        · rcases p281_3 (m.d 1 2) (by simp) with h286 | h286
                          · linarith only [h0, h286, hlam]
                          · linarith only [h271, h286, hlam]
                        · linarith only [h285, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        rcases p281_3 (m.d 0 2) (by simp) with h290 | h290
                        · rcases p281_3 (m.d 1 2) (by simp) with h291 | h291
                          · linarith only [h0, h291, hlam]
                          · linarith only [h272, h291, hlam]
                        · linarith only [h290, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, hlam, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h7, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h275, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, h2, h275, h277, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h2, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, h2, h275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h0, h2, h275, h277, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h3, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h271, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h275, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h277, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h4, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h272, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h276, hlam, p281_0]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [h272, h275, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p281_1]
                      · have p281_0 := h281c.1
                        have p281_1 := h281c.2.1
                        have p281_2 := h281c.2.2.1
                        have p281_3 := h281c.2.2.2
                        linarith only [hlam, p281_0]
                · linarith only [h272, h274, h276, h7, hlam]
              · linarith only [h0, h2, h272, h275, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h271, h274, h6, h7, hc24, hlam, hphi, ht45, u5elo0]
          · linarith only [h271, h273, h7, hlam]
        · linarith only [h271, h272, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
        · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
          · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
            · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
              · rcases m.htr 2 3 5 (by decide) (by decide) with h324 | h324
                · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                    · rcases h2bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h320, h324, h326, hc01, hc45, hlam, hphi, ht0b, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h271, h320, h323, h324, h326, hc01, hc45, hlam, hphi, ht0b, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h271, h320, h324, h326, hc01, hc45, hlam, hphi, ht0b, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        rcases p327_3 (m.d 0 2) (by simp) with h332 | h332
                        · rcases p327_3 (m.d 1 2) (by simp) with h333 | h333
                          · linarith only [h0, h333, hlam]
                          · linarith only [h320, h333, hlam]
                        · linarith only [h332, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, hlam, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h7, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h271, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h271, h323, h324, h326, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h2, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h2, h324, h326, hc01, hc45, hlam, hphi, ht0b, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h3, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h320, h324, h326, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h323, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h0, h2, h323, h324, h326, hc01, hc45, hlam, hphi, ht0b, ht5b, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h4, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h320, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h324, hlam, p327_0]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [h325, hlam, p327_1]
                      · have p327_0 := h327c.1
                        have p327_1 := h327c.2.1
                        have p327_2 := h327c.2.2.1
                        have p327_3 := h327c.2.2.2
                        linarith only [hlam, p327_0]
                    · linarith only [h0, h2, h320, h325, h326, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h271, h325, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h271, h320, h322, h323, h324, hc25, hlam, hphi, u5elo1]
              · linarith only [h0, h2, h320, h323, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h271, h320, h321, h322, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
            · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
              · linarith only [h0, h2, h321, h362, h363, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h2, h320, h363, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h320, h362, h7, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
          · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
            · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
              · rcases m.htr 2 3 5 (by decide) (by decide) with h370 | h370
                · rcases m.htr 2 4 5 (by decide) (by decide) with h371 | h371
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h372 | h372
                    · rcases h2bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        rcases p373_3 (m.d 0 2) (by simp) with h375 | h375
                        · rcases p373_3 (m.d 1 2) (by simp) with h376 | h376
                          · linarith only [h0, h376, hlam]
                          · rcases p373_3 (m.d 2 3) (by simp) with h378 | h378
                            · linarith only [h2, h378, hlam]
                            · linarith only [h378, h7, hlam]
                        · linarith only [h0, h375, hlam]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, h367, h372, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, h271, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, h320, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, hlam, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h7, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h271, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h320, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h2, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, h2, h271, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, h2, h320, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h3, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h369, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h0, h2, h320, h369, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h4, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h370, hlam, p373_0]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [h371, hlam, p373_1]
                      · have p373_0 := h373c.1
                        have p373_1 := h373c.2.1
                        have p373_2 := h373c.2.2.1
                        have p373_3 := h373c.2.2.2
                        linarith only [hlam, p373_0]
                    · rcases h2bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        rcases p405_3 (m.d 0 2) (by simp) with h407 | h407
                        · rcases p405_3 (m.d 1 2) (by simp) with h408 | h408
                          · linarith only [h0, h408, hlam]
                          · rcases p405_3 (m.d 2 3) (by simp) with h410 | h410
                            · linarith only [h2, h410, hlam]
                            · linarith only [h410, h7, hlam]
                        · linarith only [h0, h407, hlam]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h369, h371, h372, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h371, h372, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h320, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, hlam, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h7, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h271, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h320, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h2, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h2, h371, h372, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h2, h320, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h3, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h369, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h2, h320, h369, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h4, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h370, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h371, hlam, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                  · linarith only [h271, h371, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h370, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h367, h369, h7, hlam]
            · linarith only [h367, h368, h6, hc34, hlam, hphi, ht45, u5elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h441 | h441
            · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
              · linarith only [h0, h2, h367, h441, h442, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h444 | h444
                · rcases m.htr 2 4 5 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h446 | h446
                    · rcases h2bigk with h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        rcases p447_3 (m.d 0 2) (by simp) with h449 | h449
                        · rcases p447_3 (m.d 1 2) (by simp) with h450 | h450
                          · linarith only [h0, h450, hlam]
                          · rcases p447_3 (m.d 2 3) (by simp) with h452 | h452
                            · linarith only [h2, h452, hlam]
                            · linarith only [h452, h7, hlam]
                        · linarith only [h0, h449, hlam]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h320, h444, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h320, h442, h444, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h320, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, hlam, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h7, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h271, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h320, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h2, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h442, hlam, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h2, h320, h442, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h3, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h2, h442, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h2, h442, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h0, h2, h320, h442, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h4, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h444, hc12, hc23, hlam, hphi, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h444, hlam, p447_0]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [h445, hlam, p447_1]
                      · have p447_0 := h447c.1
                        have p447_1 := h447c.2.1
                        have p447_2 := h447c.2.2.1
                        have p447_3 := h447c.2.2.2
                        linarith only [hlam, p447_0]
                    · linarith only [h442, h446, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h271, h445, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h444, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
              · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
                · rcases m.htr 2 4 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h485 | h485
                    · rcases h2bigk with h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        rcases p486_3 (m.d 0 2) (by simp) with h488 | h488
                        · rcases p486_3 (m.d 1 2) (by simp) with h489 | h489
                          · linarith only [h0, h489, hlam]
                          · rcases p486_3 (m.d 2 3) (by simp) with h491 | h491
                            · linarith only [h2, h491, hlam]
                            · linarith only [h491, h7, hlam]
                        · linarith only [h0, h488, hlam]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h0, h441, h482, h485, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h0, h441, h483, h484, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h0, h441, h483, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h0, hlam, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h7, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h271, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h320, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h2, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h0, h2, h441, h483, h484, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h0, h2, h441, h483, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h3, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h482, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h3, h441, h483, h5, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h4, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h483, hlam, p486_0]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [h484, hlam, p486_1]
                      · have p486_0 := h486c.1
                        have p486_1 := h486c.2.1
                        have p486_2 := h486c.2.2.1
                        have p486_3 := h486c.2.2.2
                        linarith only [hlam, p486_0]
                    · linarith only [h367, h485, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h271, h484, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h483, h6, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
                · linarith only [h441, h482, h521, h7, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h521, h6, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
  · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]

end R2N4
