import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
          · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h12, h15, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h12, h14, h15, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h12, h14, h18, hlam]
                    · rcases h3bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p20_1, u1ehi2]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h13, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        rcases p20_3 (m.d 0 3) (by simp) with h24 | h24
                        · rcases p20_3 (m.d 1 3) (by simp) with h25 | h25
                          · linarith only [h1, h25, hlam]
                          · linarith only [h25, h9, hlam]
                        · linarith only [h24, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        rcases p20_3 (m.d 0 3) (by simp) with h29 | h29
                        · rcases p20_3 (m.d 1 3) (by simp) with h30 | h30
                          · linarith only [h1, h30, hlam]
                          · linarith only [h10, h30, hlam]
                        · linarith only [h29, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h1, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h13, h18, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h18, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h3, hlam, p20_0]
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
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h18, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
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
                        linarith only [h18, hlam, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h5, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h10, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h13, hlam, p20_0]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                      · have p20_0 := h20c.1
                        have p20_1 := h20c.2.1
                        have p20_2 := h20c.2.2.1
                        have p20_3 := h20c.2.2.2
                        linarith only [hlam, p20_0]
                · linarith only [h0, h10, h12, h13, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h12, h55, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                    · rcases h3bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h3, h55, h58, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        rcases p59_3 (m.d 0 3) (by simp) with h62 | h62
                        · rcases p59_3 (m.d 1 3) (by simp) with h63 | h63
                          · linarith only [h1, h63, hlam]
                          · linarith only [h63, h7, hlam]
                        · linarith only [h3, h62, hlam]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h3, h55, h58, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h3, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h1, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h55, h58, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h55, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h3, hlam, p59_0]
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
                        linarith only [h12, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h55, hlam, p59_0]
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
                        linarith only [hc23, hc34, hlam, hphi, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h0, h55, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h5, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h10, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h58, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                    · linarith only [h12, h57, h58, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h57, h7, h9, h90, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h11, h12, h7, h9, h90, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
              · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                  · linarith only [h11, h95, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                    · linarith only [h11, h93, h97, hc23, hlam, hphi, ht12, u1ehi3]
                    · rcases h3bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h3, h94, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        rcases p99_3 (m.d 0 3) (by simp) with h103 | h103
                        · rcases p99_3 (m.d 1 3) (by simp) with h104 | h104
                          · linarith only [h1, h104, hlam]
                          · linarith only [h104, h9, hlam]
                        · linarith only [h103, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        rcases p99_3 (m.d 0 3) (by simp) with h108 | h108
                        · rcases p99_3 (m.d 1 3) (by simp) with h109 | h109
                          · linarith only [h1, h109, hlam]
                          · linarith only [h10, h109, hlam]
                        · linarith only [h108, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h1, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h94, h97, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h7, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h3, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h7, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h7, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h4, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h9, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h93, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h97, hlam, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h5, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h10, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h94, hlam, p99_0]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                      · have p99_0 := h99c.1
                        have p99_1 := h99c.2.1
                        have p99_2 := h99c.2.2.1
                        have p99_3 := h99c.2.2.2
                        linarith only [hlam, p99_0]
                · linarith only [h0, h10, h7, h93, h94, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h134 | h134
                · linarith only [h0, h11, h134, h3, h4, h6, h9, h93, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                  · linarith only [h11, h136, h9, h93, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                    · linarith only [h11, h138, h9, hlam]
                    · rcases h3bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p140_1, u1ehi2]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        rcases p140_3 (m.d 0 3) (by simp) with h143 | h143
                        · rcases p140_3 (m.d 1 3) (by simp) with h144 | h144
                          · linarith only [h1, h144, hlam]
                          · linarith only [h144, h7, hlam]
                        · linarith only [h143, h3, hlam]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h3, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h138, h3, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h1, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h7, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h138, h7, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h3, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h7, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h93, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h134, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h4, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h9, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h138, hlam, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h5, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h10, hlam, p140_0]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h10, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [h0, h10, h7, h93, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p140_1]
                      · have p140_0 := h140c.1
                        have p140_1 := h140c.2.1
                        have p140_2 := h140c.2.2.1
                        have p140_3 := h140c.2.2.2
                        linarith only [hlam, p140_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
            · linarith only [h10, h170, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
              · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                · linarith only [h10, h173, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
                  · linarith only [h170, h175, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                    · linarith only [h170, h177, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h3bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p179_1, u1ehi3]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h172, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        rcases p179_3 (m.d 0 3) (by simp) with h183 | h183
                        · rcases p179_3 (m.d 1 3) (by simp) with h184 | h184
                          · linarith only [h1, h184, hlam]
                          · linarith only [h184, h9, hlam]
                        · linarith only [h183, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h10, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p179_1, u1ehi3]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h1, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h172, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h10, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h10, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h3, hlam, p179_0]
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
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h173, hlam, p179_0]
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
                        linarith only [h172, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h177, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h5, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p179_1, u1ehi2]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h177, h3, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
              · linarith only [h10, h172, h9, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
          · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
            · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
              · linarith only [h210, h212, h9, hc23, hlam, hphi, ht12, u1ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h214 | h214
                · rcases m.htr 2 4 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                    · rcases h3bigk with h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h210, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p217_1, u1ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h214, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h210, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p217_1, u1ehi4]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        rcases p217_3 (m.d 0 3) (by simp) with h222 | h222
                        · rcases p217_3 (m.d 1 3) (by simp) with h223 | h223
                          · linarith only [h1, h223, hlam]
                          · linarith only [h210, h223, hlam]
                        · linarith only [h222, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h1, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h214, h216, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h9, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h216, h3, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h3, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h7, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h212, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h216, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h4, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p217_1, u1ehi2]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h216, h3, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h5, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h210, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h214, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h216, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                    · linarith only [h216, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · linarith only [h0, h210, h211, h212, h214, h215, h3, h4, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h210, h214, h3, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h210, h211, h9, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
            · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
              · linarith only [h252, h7, h9, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h254 | h254
                · linarith only [h210, h254, h7, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h257 | h257
                    · rcases h3bigk with h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c | h258c
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p258_1, u1ehi2]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        rcases p258_3 (m.d 0 3) (by simp) with h261 | h261
                        · rcases p258_3 (m.d 1 3) (by simp) with h262 | h262
                          · linarith only [h1, h262, hlam]
                          · linarith only [h262, h7, hlam]
                        · linarith only [h261, h3, hlam]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h210, h257, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p258_1, u1ehi2]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h210, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p258_1, u1ehi2]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h1, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h210, h257, hc23, hc34, hlam, hphi, p258_1]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h9, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h210, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h3, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h7, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h252, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h254, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h4, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p258_1, u1ehi2]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p258_1]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p258_1]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h5, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [hc35, hlam, hphi, ht12, ht23, p258_1, u1ehi2]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p258_1]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [h257, hlam, p258_0]
                      · have p258_0 := h258c.1
                        have p258_1 := h258c.2.1
                        have p258_2 := h258c.2.2.1
                        have p258_3 := h258c.2.2.2
                        linarith only [hlam, p258_0]
                    · linarith only [h0, h256, h257, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                    · rcases h3bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p290_1, u1ehi2]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        rcases p290_3 (m.d 0 3) (by simp) with h293 | h293
                        · rcases p290_3 (m.d 1 3) (by simp) with h294 | h294
                          · linarith only [h1, h294, hlam]
                          · linarith only [h294, h7, hlam]
                        · linarith only [h293, h3, hlam]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p290_1, u1ehi2]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h210, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p290_1, u1ehi2]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h1, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h9, hc23, hc34, hlam, hphi, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h9, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h210, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h3, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h7, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h252, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h254, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h4, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h210, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p290_1, u1ehi2]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h5, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hc35, hlam, hphi, ht12, ht23, p290_1, u1ehi2]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h289, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                    · linarith only [h251, h289, h9, hc14, hlam, hphi, u1ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
              · linarith only [h321, h7, h9, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                · linarith only [h210, h323, h7, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                  · linarith only [h251, h325, h9, hc24, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
                    · linarith only [h0, h251, h3, h327, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · linarith only [h0, h3, h327, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
        · linarith only [h330, h7, h8, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
          · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
            · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
              · linarith only [h330, h334, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                · linarith only [h0, h3, h334, h336, h4, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3, h332, h334, h336, h4, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h332, h333, h7, h8, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
            · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
              · linarith only [h330, h341, h7, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                · linarith only [h0, h3, h332, h341, h343, h4, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                    · rcases h3bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi2]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        rcases p347_3 (m.d 0 3) (by simp) with h350 | h350
                        · rcases p347_3 (m.d 1 3) (by simp) with h351 | h351
                          · linarith only [h1, h351, hlam]
                          · linarith only [h351, h7, hlam]
                        · linarith only [h3, h350, hlam]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, h341, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, h332, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p347_1, u1ehi2]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h1, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h332, hc23, hc35, hlam, hphi, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h330, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h332, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h3, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h7, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h341, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h343, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h4, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h5, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hc35, hlam, hphi, ht12, ht23, p347_1, u1ehi2]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [h346, hlam, p347_0]
                      · have p347_0 := h347c.1
                        have p347_1 := h347c.2.1
                        have p347_2 := h347c.2.2.1
                        have p347_3 := h347c.2.2.2
                        linarith only [hlam, p347_0]
                    · linarith only [h340, h341, h346, h8, hc14, hlam, hphi, u1ehi1]
                  · linarith only [h340, h345, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
              · linarith only [h0, h3, h340, h379, h4, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                · linarith only [h0, h3, h340, h381, h4, h6, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                  · linarith only [h340, h383, h7, h8, hc24, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h0, h3, h383, h4, h6, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
      · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
        · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
          · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
            · rcases m.htr 2 3 4 (by decide) (by decide) with h390 | h390
              · rcases m.htr 2 3 5 (by decide) (by decide) with h391 | h391
                · rcases m.htr 2 4 5 (by decide) (by decide) with h392 | h392
                  · linarith only [h0, h3, h386, h392, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h3, h386, h389, h392, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h386, h388, h389, h391, h7, hc13, hlam, hphi, u1ehi4]
              · linarith only [h386, h389, h390, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
              · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h0, h3, h386, h399, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h401 | h401
                    · linarith only [h0, h3, h386, h389, h397, h401, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h3bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p403_1, u1ehi2]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        rcases p403_3 (m.d 0 3) (by simp) with h407 | h407
                        · rcases p403_3 (m.d 1 3) (by simp) with h408 | h408
                          · linarith only [h1, h408, hlam]
                          · linarith only [h387, h408, hlam]
                        · linarith only [h407, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        rcases p403_3 (m.d 0 3) (by simp) with h412 | h412
                        · rcases p403_3 (m.d 1 3) (by simp) with h413 | h413
                          · linarith only [h1, h413, hlam]
                          · linarith only [h388, h413, hlam]
                        · linarith only [h412, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h1, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h7, hlam, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, h401, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h3, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, h401, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h4, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h387, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h397, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h401, hlam, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h5, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h388, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h398, hlam, p403_0]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p403_1]
                      · have p403_0 := h403c.1
                        have p403_1 := h403c.2.1
                        have p403_2 := h403c.2.2.1
                        have p403_3 := h403c.2.2.2
                        linarith only [hlam, p403_0]
                · linarith only [h386, h388, h398, h7, hc13, hlam, hphi, u1ehi3]
              · linarith only [h0, h3, h386, h397, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h439 | h439
            · linarith only [h386, h388, h439, h7, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h441 | h441
              · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
                · linarith only [h386, h388, h442, h7, hc23, hlam, hphi, ht12, u1ehi3]
                · linarith only [h0, h3, h386, h442, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
              · linarith only [h386, h441, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h386, h387, h7, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
        · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
          · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
            · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
              · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                    · rcases h3bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, h447, h453, hc01, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, h386, h450, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, h453, hc01, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        rcases p454_3 (m.d 0 3) (by simp) with h459 | h459
                        · rcases p454_3 (m.d 1 3) (by simp) with h460 | h460
                          · linarith only [h1, h460, hlam]
                          · linarith only [h448, h460, hlam]
                        · linarith only [h459, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h1, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h7, hlam, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h453, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h3, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, h453, hc01, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h4, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h447, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h450, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h447, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h5, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h448, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h451, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h453, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                    · rcases h3bigk with h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p484_1, u1ehi2]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, h386, h450, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        rcases p484_3 (m.d 0 3) (by simp) with h488 | h488
                        · rcases p484_3 (m.d 1 3) (by simp) with h489 | h489
                          · linarith only [h1, h489, hlam]
                          · linarith only [h447, h489, hlam]
                        · linarith only [h488, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        rcases p484_3 (m.d 0 3) (by simp) with h493 | h493
                        · rcases p484_3 (m.d 1 3) (by simp) with h494 | h494
                          · linarith only [h1, h494, hlam]
                          · linarith only [h448, h494, hlam]
                        · linarith only [h493, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h1, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h7, hlam, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, h453, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h3, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, h453, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h4, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h447, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h450, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h453, hlam, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h5, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h448, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h451, hlam, p484_0]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p484_1]
                      · have p484_0 := h484c.1
                        have p484_1 := h484c.2.1
                        have p484_2 := h484c.2.2.1
                        have p484_3 := h484c.2.2.2
                        linarith only [hlam, p484_0]
                  · linarith only [h386, h452, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h448, h451, h7, hlam]
              · linarith only [h0, h3, h4, h450, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h521 | h521
              · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                  · linarith only [h449, h521, h523, hc23, hlam, hphi, ht12, u1ehi3]
                  · linarith only [h386, h523, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h448, h522, h7, hlam]
              · linarith only [h0, h3, h4, h521, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
            · linarith only [h447, h448, h528, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
              · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                · linarith only [h448, h531, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h0, h3, h5, h531, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h0, h3, h447, h448, h5, h530, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h535 | h535
          · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
            · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
              · linarith only [h447, h537, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h537, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h447, h535, h536, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h541 | h541
            · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
              · linarith only [h0, h3, h447, h542, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h0, h3, h4, h542, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
              · linarith only [h447, h545, h7, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h0, h3, h4, h545, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
    · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
      · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
        · rcases m.htr 1 3 5 (by decide) (by decide) with h551 | h551
          · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
            · linarith only [h2, h552, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
              · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                · rcases m.htr 2 4 5 (by decide) (by decide) with h556 | h556
                  · linarith only [h2, h548, h554, h556, h6, hc12, hlam, hphi, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                    · linarith only [h2, h558, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h3bigk with h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h3, h548, h555, h558, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h3, h555, h558, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        rcases p560_3 (m.d 0 3) (by simp) with h564 | h564
                        · rcases p560_3 (m.d 1 3) (by simp) with h565 | h565
                          · linarith only [h1, h565, hlam]
                          · linarith only [h550, h565, hlam]
                        · linarith only [h564, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        rcases p560_3 (m.d 0 3) (by simp) with h569 | h569
                        · rcases p560_3 (m.d 1 3) (by simp) with h570 | h570
                          · linarith only [h1, h570, hlam]
                          · linarith only [h551, h570, hlam]
                        · linarith only [h569, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h1, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h555, h558, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h548, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h548, h558, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h3, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h548, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h548, h558, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h4, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h550, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h554, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h558, hlam, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h5, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h551, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h555, hlam, p560_0]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p560_1]
                      · have p560_0 := h560c.1
                        have p560_1 := h560c.2.1
                        have p560_2 := h560c.2.2.1
                        have p560_3 := h560c.2.2.2
                        linarith only [hlam, p560_0]
                · linarith only [h0, h548, h551, h554, h555, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h595 | h595
                · linarith only [h0, h548, h550, h554, h595, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h597 | h597
                  · linarith only [h2, h597, h6, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                    · linarith only [h2, h550, h599, h6, hlam]
                    · rcases h3bigk with h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h3, h551, h554, h599, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 3) (by simp) with h604 | h604
                        · rcases p601_3 (m.d 1 3) (by simp) with h605 | h605
                          · linarith only [h1, h605, hlam]
                          · linarith only [h548, h605, hlam]
                        · linarith only [h3, h604, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h3, h554, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h3, h554, h599, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h1, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h548, h554, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h548, h554, h599, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h3, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h548, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h554, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h595, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h4, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h550, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h599, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h5, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h551, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h548, h551, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, h548, h551, h554, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h631 | h631
            · linarith only [h5, h551, h6, h631, hc14, hlam, hphi, u1ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h633 | h633
              · rcases m.htr 2 3 5 (by decide) (by decide) with h634 | h634
                · linarith only [h550, h551, h634, hc23, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h636 | h636
                  · linarith only [h2, h6, h636, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
                    · linarith only [h5, h550, h551, h6, h638, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h3bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h550, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p640_1, u1ehi3]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        rcases p640_3 (m.d 0 3) (by simp) with h644 | h644
                        · rcases p640_3 (m.d 1 3) (by simp) with h645 | h645
                          · linarith only [h1, h645, hlam]
                          · linarith only [h550, h645, hlam]
                        · linarith only [h644, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h550, h551, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p640_1, u1ehi3]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h1, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h5, h551, h633, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h5, h551, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h551, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h3, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h548, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h634, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h4, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h550, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h633, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h638, hlam, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h5, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
              · linarith only [h0, h3, h5, h550, h551, h633, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h4, h550, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h672 | h672
        · linarith only [h548, h549, h672, hlam]
        · linarith only [h4, h6, h672, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
      · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
        · rcases m.htr 1 3 5 (by decide) (by decide) with h677 | h677
          · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
            · linarith only [h0, h3, h548, h6, h675, h678, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h680 | h680
              · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
                · rcases m.htr 2 4 5 (by decide) (by decide) with h682 | h682
                  · linarith only [h0, h2, h3, h548, h6, h675, h682, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h684 | h684
                    · linarith only [h0, h2, h3, h548, h6, h675, h680, h684, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h3bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h0, h3, h548, h675, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h0, h3, h548, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p686_1, u1ehi1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        rcases p686_3 (m.d 0 3) (by simp) with h690 | h690
                        · rcases p686_3 (m.d 1 3) (by simp) with h691 | h691
                          · linarith only [h1, h691, hlam]
                          · linarith only [h676, h691, hlam]
                        · linarith only [h690, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        rcases p686_3 (m.d 0 3) (by simp) with h695 | h695
                        · rcases p686_3 (m.d 1 3) (by simp) with h696 | h696
                          · linarith only [h1, h696, hlam]
                          · linarith only [h677, h696, hlam]
                        · linarith only [h695, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h1, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h548, hlam, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h3, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hc23, hlam, hphi, ht12, p686_1, u1ehi2]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h0, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h4, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h676, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h680, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h684, hlam, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h5, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h677, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h681, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h0, h3, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                · linarith only [h548, h675, h677, h681, hc13, hlam, hphi, u1ehi3]
              · linarith only [h4, h548, h6, h680, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h722 | h722
            · linarith only [h5, h6, h675, h677, h722, hc12, hlam, hphi, u1ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h724 | h724
              · rcases m.htr 2 3 5 (by decide) (by decide) with h725 | h725
                · linarith only [h0, h3, h548, h675, h677, h725, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                · linarith only [h548, h675, h725, hc35, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h548, h675, h724, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h4, h548, h6, h675, h676, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h730 | h730
        · rcases m.htr 1 3 5 (by decide) (by decide) with h731 | h731
          · rcases m.htr 1 4 5 (by decide) (by decide) with h732 | h732
            · linarith only [h2, h6, h732, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
              · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
                · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                  · linarith only [h0, h2, h3, h6, h675, h734, h736, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · linarith only [h675, h736, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h548, h731, h735, hc13, hlam, hphi, u1ehi1]
              · linarith only [h4, h548, h6, h734, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h741 | h741
            · linarith only [h2, h6, h741, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
              · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                · linarith only [h0, h3, h730, h731, h744, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h548, h744, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h548, h743, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h4, h6, h730, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]

end R2N4
