import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
            · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
              · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h10, h15, h17, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h17, h21, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · rcases h0bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h0, h10, h16, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h17, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      rcases p23_3 (m.d 0 1) (by simp) with h28 | h28
                      · rcases p23_3 (m.d 0 2) (by simp) with h29 | h29
                        · linarith only [h0, h29, hlam]
                        · linarith only [h29, h6, hlam]
                      · linarith only [h28, h3, hlam]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h0, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h17, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h0, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      rcases p23_3 (m.d 0 1) (by simp) with h37 | h37
                      · rcases p23_3 (m.d 0 2) (by simp) with h38 | h38
                        · rcases p23_3 (m.d 0 3) (by simp) with h39 | h39
                          · linarith only [h39, h4, hlam]
                          · linarith only [h39, h8, hlam]
                        · linarith only [h38, h6, hlam]
                      · linarith only [h3, h37, hlam]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h1, hlam, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h4, hlam, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h17, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h17, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p23_1, u3elo0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h2, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h5, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h7, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h17, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p23_1, u3elo0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h3, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h6, hlam, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h8, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h9, hlam, p23_1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
              · linarith only [h16, h8, hc23, hlam, hphi, u3elo0]
            · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
          · linarith only [h14, h8, hc13, hlam, hphi, u3elo0]
        · linarith only [h10, h13, h7, hc23, hlam, hphi, u3elo0]
      · linarith only [h10, h12, h6, h8, hc23, hlam, hphi, u3elo0]
    · linarith only [h10, h11, h5, h7, hc23, hlam, hphi, u3elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
    · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
      · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
        · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
            · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                · linarith only [h10, h65, h71, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                  · linarith only [h69, h71, h73, hlam]
                  · rcases h0bigk with h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [hlam, p75_0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h10, h4, h66, h69, h71, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h10, h4, h66, h69, h71, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h69, h71, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      rcases p75_3 (m.d 0 1) (by simp) with h80 | h80
                      · rcases p75_3 (m.d 0 2) (by simp) with h81 | h81
                        · linarith only [h0, h81, hlam]
                        · linarith only [h6, h81, hlam]
                      · linarith only [h3, h80, hlam]
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
                      linarith only [h10, h4, h66, h69, h71, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h0, h69, h71, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      rcases p75_3 (m.d 0 1) (by simp) with h89 | h89
                      · rcases p75_3 (m.d 0 2) (by simp) with h90 | h90
                        · rcases p75_3 (m.d 0 3) (by simp) with h91 | h91
                          · linarith only [h4, h91, hlam]
                          · linarith only [h8, h91, hlam]
                        · linarith only [h6, h90, hlam]
                      · linarith only [h3, h89, hlam]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h1, hlam, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h4, hlam, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [hlam, p75_0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h69, h71, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p75_1, u3elo0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h69, h71, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p75_1, u3elo0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h2, hlam, p75_0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h5, hlam, p75_0]
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
                      linarith only [h69, h7, h71, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p75_1, u3elo0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h3, hlam, p75_0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h6, hlam, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h8, hlam, p75_0]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [h9, hlam, p75_1]
                    · have p75_0 := h75c.1
                      have p75_1 := h75c.2.1
                      have p75_2 := h75c.2.2.1
                      have p75_3 := h75c.2.2.2
                      linarith only [hlam, p75_0]
              · linarith only [h10, h70, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h10, h69, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h68, h8, hc13, hlam, hphi, u3elo0]
        · linarith only [h10, h65, h67, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
        · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
          · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
            · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
              · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                · linarith only [h118, h119, h65, h66, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h117, h119, h65, h66, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · linarith only [h116, h118, hc23, hlam, hphi, u3elo1]
            · linarith only [h10, h117, h7, hc13, hlam, hphi, u3elo0]
          · linarith only [h10, h116, h8, hc12, hlam, hphi, ht23, u3elo0]
        · linarith only [h10, h115, h65, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
      · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
        · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
          · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
            · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
              · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                  · rcases h0bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h126, h129, h130, h132, h4, h65, hc01, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h1, h127, h132, hc01, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h126, h130, h132, h5, h65, hc01, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      rcases p133_3 (m.d 0 1) (by simp) with h138 | h138
                      · rcases p133_3 (m.d 0 2) (by simp) with h139 | h139
                        · linarith only [h0, h139, hlam]
                        · linarith only [h139, h6, hlam]
                      · linarith only [h138, h3, hlam]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h0, hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h126, h129, h130, h132, h4, h65, hc02, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h0, h126, h130, h132, h5, h65, hc01, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      rcases p133_3 (m.d 0 1) (by simp) with h147 | h147
                      · rcases p133_3 (m.d 0 2) (by simp) with h148 | h148
                        · rcases p133_3 (m.d 0 3) (by simp) with h149 | h149
                          · linarith only [h149, h4, hlam]
                          · linarith only [h149, h8, hlam]
                        · linarith only [h148, h6, hlam]
                      · linarith only [h147, h3, hlam]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h1, hlam, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h4, hlam, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h126, h130, h132, h5, h65, hc03, hc45, hlam, hphi, ht0b, ht5b, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      rcases p133_3 (m.d 0 1) (by simp) with h158 | h158
                      · rcases p133_3 (m.d 0 2) (by simp) with h159 | h159
                        · rcases p133_3 (m.d 0 3) (by simp) with h160 | h160
                          · rcases p133_3 (m.d 0 4) (by simp) with h161 | h161
                            · linarith only [h161, h7, hlam]
                            · linarith only [h161, h9, hlam]
                          · linarith only [h160, h8, hlam]
                        · linarith only [h159, h6, hlam]
                      · linarith only [h158, h3, hlam]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h2, hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h5, hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h7, hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      rcases p133_3 (m.d 0 1) (by simp) with h171 | h171
                      · rcases p133_3 (m.d 0 2) (by simp) with h172 | h172
                        · rcases p133_3 (m.d 0 3) (by simp) with h173 | h173
                          · rcases p133_3 (m.d 0 4) (by simp) with h174 | h174
                            · rcases p133_3 (m.d 0 5) (by simp) with h175 | h175
                              · linarith only [h175, h9, hlam]
                              · rcases h0emin with h177 | h177 | h177 | h177 | h177
                                · rcases h2bigk with h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    rcases p178_3 (m.d 0 2) (by simp) with h180 | h180
                                    · rcases p178_3 (m.d 1 2) (by simp) with h181 | h181
                                      · linarith only [h0, h181, hlam]
                                      · rcases p178_3 (m.d 2 3) (by simp) with h183 | h183
                                        · linarith only [h183, h4, hlam]
                                        · linarith only [h10, h183, hlam]
                                    · linarith only [h0, h180, hlam]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h0, h126, h129, h130, h132, h65, hc01, hc45, hlam, hphi, ht0b, ht5b, p178_1]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h0, h126, h130, h132, h65, hc01, hc45, hlam, hphi, ht0b, ht5b, p178_1]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h126, h129, h4, h65, hlam, p178_2]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h0, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h10, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h65, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h129, h130, h132, h65, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p178_1, u3elo2]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h4, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h4, hc12, hlam, hphi, ht23, p178_1, u3elo0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h4, h65, hc12, hlam, hphi, ht23, p178_1, u3elo0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    rcases p178_3 (m.d 0 2) (by simp) with h199 | h199
                                    · rcases p178_3 (m.d 1 2) (by simp) with h200 | h200
                                      · linarith only [h10, h200, hlam]
                                      · linarith only [h126, h200, hlam]
                                    · linarith only [h199, h6, hlam]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h5, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h126, h130, h132, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p178_1]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h129, hlam, p178_1]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    rcases p178_3 (m.d 0 2) (by simp) with h208 | h208
                                    · rcases p178_3 (m.d 1 2) (by simp) with h209 | h209
                                      · linarith only [h209, h65, hlam]
                                      · linarith only [h126, h209, hlam]
                                    · linarith only [h208, h6, hlam]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h6, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h126, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h130, hlam, p178_1]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [h131, hlam, p178_0]
                                  · have p178_0 := h178c.1
                                    have p178_1 := h178c.2.1
                                    have p178_2 := h178c.2.2.1
                                    have p178_3 := h178c.2.2.2
                                    linarith only [hlam, p178_0]
                                · rcases h2bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    rcases p218_3 (m.d 0 2) (by simp) with h220 | h220
                                    · rcases p218_3 (m.d 1 2) (by simp) with h221 | h221
                                      · linarith only [h0, h221, hlam]
                                      · rcases p218_3 (m.d 2 3) (by simp) with h223 | h223
                                        · linarith only [h223, h4, hlam]
                                        · linarith only [h10, h223, hlam]
                                    · linarith only [h0, h220, hlam]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h0, h10, h126, h130, h132, hc01, hc45, hlam, hphi, ht0b, ht5b, p218_1]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h0, h126, h130, h132, h65, hc01, hc45, hlam, hphi, ht0b, ht5b, p218_1]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h10, h126, h4, hlam, p218_2]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h0, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h10, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h65, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h10, h130, h132, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p218_1, u3elo2]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h4, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, p218_1, u3elo2]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h126, h130, h132, h4, h65, hc02, hc45, hlam, hphi, ht0b, ht5b, p218_1]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    rcases p218_3 (m.d 0 2) (by simp) with h239 | h239
                                    · rcases p218_3 (m.d 1 2) (by simp) with h240 | h240
                                      · linarith only [h10, h240, hlam]
                                      · linarith only [h126, h240, hlam]
                                    · linarith only [h239, h6, hlam]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h5, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h0, h126, h130, h132, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p218_1]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h129, hlam, p218_1]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    rcases p218_3 (m.d 0 2) (by simp) with h248 | h248
                                    · rcases p218_3 (m.d 1 2) (by simp) with h249 | h249
                                      · linarith only [h249, h65, hlam]
                                      · linarith only [h126, h249, hlam]
                                    · linarith only [h248, h6, hlam]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h6, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h126, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h130, hlam, p218_1]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [h131, hlam, p218_0]
                                  · have p218_0 := h218c.1
                                    have p218_1 := h218c.2.1
                                    have p218_2 := h218c.2.2.1
                                    have p218_3 := h218c.2.2.2
                                    linarith only [hlam, p218_0]
                                · linarith only [h177, hlam, ht01, ht12, ht23, u3elo0]
                                · linarith only [h177, h7, hlam, ht01, ht12, ht23, u3elo0]
                                · linarith only [h177, h7, hlam, ht01, ht12, ht23, p133_1, u3elo0]
                            · linarith only [h174, h9, hlam]
                          · linarith only [h173, h8, hlam]
                        · linarith only [h172, h6, hlam]
                      · linarith only [h171, h3, hlam]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h3, hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h6, hlam, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h8, hlam, p133_0]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [h9, hlam, p133_1]
                    · have p133_0 := h133c.1
                      have p133_1 := h133c.2.1
                      have p133_2 := h133c.2.2.1
                      have p133_3 := h133c.2.2.2
                      linarith only [hlam, p133_0]
                  · linarith only [h10, h126, h131, h132, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h131, h65, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h130, h8, hc23, hlam, hphi, u3elo0]
            · linarith only [h10, h126, h129, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
          · linarith only [h126, h127, h128, h65, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
        · linarith only [h127, h7, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h276 | h276
        · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
          · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
            · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
              · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                  · rcases h0bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h10, h276, h281, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h1, h276, h281, hc01, hc45, hlam, hphi, ht0b, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      rcases p282_3 (m.d 0 1) (by simp) with h286 | h286
                      · rcases p282_3 (m.d 0 2) (by simp) with h287 | h287
                        · linarith only [h0, h287, hlam]
                        · linarith only [h287, h5, hlam]
                      · linarith only [h2, h286, hlam]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      rcases p282_3 (m.d 0 1) (by simp) with h291 | h291
                      · rcases p282_3 (m.d 0 2) (by simp) with h292 | h292
                        · linarith only [h0, h292, hlam]
                        · linarith only [h292, h6, hlam]
                      · linarith only [h291, h3, hlam]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h0, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h10, h276, h281, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      rcases p282_3 (m.d 0 1) (by simp) with h299 | h299
                      · rcases p282_3 (m.d 0 2) (by simp) with h300 | h300
                        · rcases p282_3 (m.d 0 3) (by simp) with h301 | h301
                          · linarith only [h301, h4, hlam]
                          · linarith only [h301, h7, hlam]
                        · linarith only [h300, h5, hlam]
                      · linarith only [h2, h299, hlam]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      rcases p282_3 (m.d 0 1) (by simp) with h306 | h306
                      · rcases p282_3 (m.d 0 2) (by simp) with h307 | h307
                        · rcases p282_3 (m.d 0 3) (by simp) with h308 | h308
                          · linarith only [h308, h4, hlam]
                          · linarith only [h308, h8, hlam]
                        · linarith only [h307, h6, hlam]
                      · linarith only [h3, h306, hlam]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h1, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h4, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h126, h6, h9, hc12, hlam, hphi, ht23, p282_1, u3elo0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h126, h6, hc12, hlam, hphi, ht23, p282_1, u3elo0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h2, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h5, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h7, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h126, h6, h7, hc12, hlam, hphi, ht23, p282_1, u3elo0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h3, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h6, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h8, hlam, p282_0]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [h9, hlam, p282_1]
                    · have p282_0 := h282c.1
                      have p282_1 := h282c.2.1
                      have p282_2 := h282c.2.2.1
                      have p282_3 := h282c.2.2.2
                      linarith only [hlam, p282_0]
                  · rcases h0bigk with h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h280, h281, h4, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h280, h281, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h280, h281, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      rcases p328_3 (m.d 0 1) (by simp) with h333 | h333
                      · rcases p328_3 (m.d 0 2) (by simp) with h334 | h334
                        · linarith only [h0, h334, hlam]
                        · linarith only [h334, h6, hlam]
                      · linarith only [h3, h333, hlam]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h0, hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h280, h281, h5, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h0, h280, h281, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      rcases p328_3 (m.d 0 1) (by simp) with h342 | h342
                      · rcases p328_3 (m.d 0 2) (by simp) with h343 | h343
                        · rcases p328_3 (m.d 0 3) (by simp) with h344 | h344
                          · linarith only [h344, h4, hlam]
                          · linarith only [h344, h8, hlam]
                        · linarith only [h343, h6, hlam]
                      · linarith only [h3, h342, hlam]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h1, hlam, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h4, hlam, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h280, h281, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p328_1, u3elo0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h126, h6, hc12, hlam, hphi, ht23, p328_1, u3elo0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h2, hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h5, hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h7, hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h126, h6, h7, hc12, hlam, hphi, ht23, p328_1, u3elo0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h3, hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h6, hlam, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h8, hlam, p328_0]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [h9, hlam, p328_1]
                    · have p328_0 := h328c.1
                      have p328_1 := h328c.2.1
                      have p328_2 := h328c.2.2.1
                      have p328_3 := h328c.2.2.2
                      linarith only [hlam, p328_0]
                · linarith only [h280, h65, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h10, h279, h8, hc13, hlam, hphi, u3elo0]
            · linarith only [h10, h278, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h277, h8, hc13, hlam, hphi, u3elo0]
        · linarith only [h10, h276, h7, hc12, hlam, hphi, ht23, u3elo0]

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h369 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
  · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
    · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
      · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
        · rcases m.htr 2 3 4 (by decide) (by decide) with h374 | h374
          · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
            · rcases m.htr 2 4 5 (by decide) (by decide) with h376 | h376
              · linarith only [h2, h370, h376, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h378 | h378
                · linarith only [h0, h369, h374, h378, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases h0bigk with h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h0, h369, h375, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p380_1]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h383 | h383
                    · rcases p380_3 (m.d 0 2) (by simp) with h384 | h384
                      · linarith only [h0, h384, hlam]
                      · linarith only [h384, h4, hlam]
                    · linarith only [h1, h383, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h388 | h388
                    · rcases p380_3 (m.d 0 2) (by simp) with h389 | h389
                      · linarith only [h0, h389, hlam]
                      · linarith only [h389, h5, hlam]
                    · linarith only [h2, h388, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h393 | h393
                    · rcases p380_3 (m.d 0 2) (by simp) with h394 | h394
                      · linarith only [h0, h394, hlam]
                      · linarith only [h394, h6, hlam]
                    · linarith only [h3, h393, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h0, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h400 | h400
                    · rcases p380_3 (m.d 0 2) (by simp) with h401 | h401
                      · rcases p380_3 (m.d 0 3) (by simp) with h402 | h402
                        · linarith only [h4, h402, hlam]
                        · rcases p380_3 (m.d 0 4) (by simp) with h404 | h404
                          · linarith only [h404, h5, hlam]
                          · rcases p380_3 (m.d 0 5) (by simp) with h406 | h406
                            · linarith only [h406, h6, hlam]
                            · rcases h0emin with h408 | h408 | h408 | h408 | h408
                              · rcases h2bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h369, h375, h378, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 2) (by simp) with h412 | h412
                                  · rcases p409_3 (m.d 1 2) (by simp) with h413 | h413
                                    · linarith only [h0, h413, hlam]
                                    · linarith only [h369, h413, hlam]
                                  · linarith only [h412, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 2) (by simp) with h417 | h417
                                  · rcases p409_3 (m.d 1 2) (by simp) with h418 | h418
                                    · linarith only [h0, h418, hlam]
                                    · linarith only [h370, h418, hlam]
                                  · linarith only [h417, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 2) (by simp) with h422 | h422
                                  · rcases p409_3 (m.d 1 2) (by simp) with h423 | h423
                                    · linarith only [h0, h423, hlam]
                                    · linarith only [h371, h423, hlam]
                                  · linarith only [h422, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h375, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 2) (by simp) with h430 | h430
                                  · rcases p409_3 (m.d 1 2) (by simp) with h431 | h431
                                    · rcases p409_3 (m.d 2 3) (by simp) with h432 | h432
                                      · linarith only [h369, h432, hlam]
                                      · linarith only [h374, h432, hlam]
                                    · linarith only [h431, hlam, p409_0]
                                  · linarith only [h430, h5, hlam]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 2) (by simp) with h437 | h437
                                  · rcases p409_3 (m.d 1 2) (by simp) with h438 | h438
                                    · rcases p409_3 (m.d 2 3) (by simp) with h439 | h439
                                      · linarith only [h369, h439, hlam]
                                      · linarith only [h375, h439, hlam]
                                    · linarith only [h438, hlam, p409_0]
                                  · linarith only [h437, h6, hlam]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h4, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h369, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h1, h369, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p380_1, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h1, h369, hc01, hc25, hlam, hphi, ht0b, ht5b, p380_1, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h5, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h370, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h374, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h376, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h6, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h371, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h375, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p380_1, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                              · rcases h2bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, h369, h375, hc01, hc35, hlam, hphi, ht0b, ht5b, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h462 | h462
                                  · rcases p459_3 (m.d 1 2) (by simp) with h463 | h463
                                    · linarith only [h0, h463, hlam]
                                    · linarith only [h369, h463, hlam]
                                  · linarith only [h462, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h467 | h467
                                  · rcases p459_3 (m.d 1 2) (by simp) with h468 | h468
                                    · linarith only [h0, h468, hlam]
                                    · linarith only [h370, h468, hlam]
                                  · linarith only [h467, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h472 | h472
                                  · rcases p459_3 (m.d 1 2) (by simp) with h473 | h473
                                    · linarith only [h0, h473, hlam]
                                    · linarith only [h371, h473, hlam]
                                  · linarith only [h472, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h480 | h480
                                  · rcases p459_3 (m.d 1 2) (by simp) with h481 | h481
                                    · rcases p459_3 (m.d 2 3) (by simp) with h482 | h482
                                      · linarith only [h369, h482, hlam]
                                      · linarith only [h374, h482, hlam]
                                    · linarith only [h481, hlam, p459_0]
                                  · linarith only [h480, h5, hlam]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h487 | h487
                                  · rcases p459_3 (m.d 1 2) (by simp) with h488 | h488
                                    · rcases p459_3 (m.d 2 3) (by simp) with h489 | h489
                                      · linarith only [h369, h489, hlam]
                                      · linarith only [h375, h489, hlam]
                                    · linarith only [h488, hlam, p459_0]
                                  · linarith only [h487, h6, hlam]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h4, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h369, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p380_1, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, h1, h369, hc01, hc25, hlam, hphi, ht0b, ht5b, p380_1, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h5, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h370, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h374, hlam, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h376, hlam, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h6, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h371, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h375, hlam, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, h374, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p380_1, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                              · linarith only [h0, h408, hc01, hlam, p380_1]
                              · linarith only [h0, h408, h8, h9, hc01, hlam, p380_1]
                              · linarith only [h0, h408, h8, hc01, hlam, p380_1]
                      · linarith only [h4, h401, hlam]
                    · linarith only [h1, h400, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h514 | h514
                    · rcases p380_3 (m.d 0 2) (by simp) with h515 | h515
                      · rcases p380_3 (m.d 0 3) (by simp) with h516 | h516
                        · linarith only [h4, h516, hlam]
                        · linarith only [h516, h7, hlam]
                      · linarith only [h5, h515, hlam]
                    · linarith only [h2, h514, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h521 | h521
                    · rcases p380_3 (m.d 0 2) (by simp) with h522 | h522
                      · rcases p380_3 (m.d 0 3) (by simp) with h523 | h523
                        · linarith only [h4, h523, hlam]
                        · linarith only [h523, h8, hlam]
                      · linarith only [h522, h6, hlam]
                    · linarith only [h3, h521, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h1, hlam, p380_1]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h4, hlam, p380_1]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h531 | h531
                    · rcases p380_3 (m.d 0 2) (by simp) with h532 | h532
                      · rcases p380_3 (m.d 0 3) (by simp) with h533 | h533
                        · rcases p380_3 (m.d 0 4) (by simp) with h534 | h534
                          · linarith only [h534, h7, hlam]
                          · rcases p380_3 (m.d 0 5) (by simp) with h536 | h536
                            · linarith only [h536, h8, hlam]
                            · linarith only [h536, h9, hlam]
                        · linarith only [h533, h7, hlam]
                      · linarith only [h5, h532, hlam]
                    · linarith only [h2, h531, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h542 | h542
                    · rcases p380_3 (m.d 0 2) (by simp) with h543 | h543
                      · rcases p380_3 (m.d 0 3) (by simp) with h544 | h544
                        · rcases p380_3 (m.d 0 4) (by simp) with h545 | h545
                          · linarith only [h545, h7, hlam]
                          · rcases p380_3 (m.d 0 5) (by simp) with h547 | h547
                            · linarith only [h547, h8, hlam]
                            · rcases h0emin with h549 | h549 | h549 | h549 | h549
                              · rcases h2bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  rcases p550_3 (m.d 0 2) (by simp) with h553 | h553
                                  · rcases p550_3 (m.d 1 2) (by simp) with h554 | h554
                                    · linarith only [h0, h554, hlam]
                                    · linarith only [h369, h554, hlam]
                                  · linarith only [h553, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  rcases p550_3 (m.d 0 2) (by simp) with h558 | h558
                                  · rcases p550_3 (m.d 1 2) (by simp) with h559 | h559
                                    · linarith only [h0, h559, hlam]
                                    · linarith only [h370, h559, hlam]
                                  · linarith only [h558, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  rcases p550_3 (m.d 0 2) (by simp) with h563 | h563
                                  · rcases p550_3 (m.d 1 2) (by simp) with h564 | h564
                                    · linarith only [h0, h564, hlam]
                                    · linarith only [h371, h564, hlam]
                                  · linarith only [h563, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h0, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h0, h375, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  rcases p550_3 (m.d 0 2) (by simp) with h571 | h571
                                  · rcases p550_3 (m.d 1 2) (by simp) with h572 | h572
                                    · rcases p550_3 (m.d 2 3) (by simp) with h573 | h573
                                      · linarith only [h369, h573, hlam]
                                      · linarith only [h374, h573, hlam]
                                    · linarith only [h572, hlam, p550_0]
                                  · linarith only [h5, h571, hlam]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  rcases p550_3 (m.d 0 2) (by simp) with h578 | h578
                                  · rcases p550_3 (m.d 1 2) (by simp) with h579 | h579
                                    · rcases p550_3 (m.d 2 3) (by simp) with h580 | h580
                                      · linarith only [h369, h580, hlam]
                                      · linarith only [h375, h580, hlam]
                                    · linarith only [h579, hlam, p550_0]
                                  · linarith only [h578, h6, hlam]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h4, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h369, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h0, h369, hc01, hc25, hlam, hphi, ht0b, ht5b, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h5, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h370, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h374, hlam, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h376, hlam, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h6, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h371, hlam, p550_0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h375, hlam, p550_1]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [h374, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p380_1, p550_1, u3elo0]
                                · have p550_0 := h550c.1
                                  have p550_1 := h550c.2.1
                                  have p550_2 := h550c.2.2.1
                                  have p550_3 := h550c.2.2.2
                                  linarith only [hlam, p550_0]
                              · rcases h2bigk with h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  rcases p600_3 (m.d 0 2) (by simp) with h603 | h603
                                  · rcases p600_3 (m.d 1 2) (by simp) with h604 | h604
                                    · linarith only [h0, h604, hlam]
                                    · linarith only [h369, h604, hlam]
                                  · linarith only [h603, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  rcases p600_3 (m.d 0 2) (by simp) with h608 | h608
                                  · rcases p600_3 (m.d 1 2) (by simp) with h609 | h609
                                    · linarith only [h0, h609, hlam]
                                    · linarith only [h370, h609, hlam]
                                  · linarith only [h608, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  rcases p600_3 (m.d 0 2) (by simp) with h613 | h613
                                  · rcases p600_3 (m.d 1 2) (by simp) with h614 | h614
                                    · linarith only [h0, h614, hlam]
                                    · linarith only [h371, h614, hlam]
                                  · linarith only [h613, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h0, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h0, h375, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  rcases p600_3 (m.d 0 2) (by simp) with h621 | h621
                                  · rcases p600_3 (m.d 1 2) (by simp) with h622 | h622
                                    · rcases p600_3 (m.d 2 3) (by simp) with h623 | h623
                                      · linarith only [h369, h623, hlam]
                                      · linarith only [h374, h623, hlam]
                                    · linarith only [h622, hlam, p600_0]
                                  · linarith only [h5, h621, hlam]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  rcases p600_3 (m.d 0 2) (by simp) with h628 | h628
                                  · rcases p600_3 (m.d 1 2) (by simp) with h629 | h629
                                    · rcases p600_3 (m.d 2 3) (by simp) with h630 | h630
                                      · linarith only [h369, h630, hlam]
                                      · linarith only [h375, h630, hlam]
                                    · linarith only [h629, hlam, p600_0]
                                  · linarith only [h6, h628, hlam]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h4, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h369, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h0, h369, hc01, hc25, hlam, hphi, ht0b, ht5b, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h5, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h370, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h374, hlam, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h376, hlam, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h6, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h371, hlam, p600_0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h375, hlam, p600_1]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [h374, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p380_1, p600_1, u3elo0]
                                · have p600_0 := h600c.1
                                  have p600_1 := h600c.2.1
                                  have p600_2 := h600c.2.2.1
                                  have p600_3 := h600c.2.2.2
                                  linarith only [hlam, p600_0]
                              · linarith only [h549, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h549, h7, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h549, hlam, ht01, ht12, ht23, p380_1, u3elo0]
                        · linarith only [h544, h8, hlam]
                      · linarith only [h543, h6, hlam]
                    · linarith only [h3, h542, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h2, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h5, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h7, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h9, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h3, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h6, hlam, p380_1]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [h8, hlam, p380_0]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    rcases p380_3 (m.d 0 1) (by simp) with h664 | h664
                    · rcases p380_3 (m.d 0 2) (by simp) with h665 | h665
                      · rcases p380_3 (m.d 0 3) (by simp) with h666 | h666
                        · rcases p380_3 (m.d 0 4) (by simp) with h667 | h667
                          · linarith only [h667, h9, hlam]
                          · rcases p380_3 (m.d 0 5) (by simp) with h669 | h669
                            · rcases h0emin with h670 | h670 | h670 | h670 | h670
                              · rcases h2bigk with h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 2) (by simp) with h674 | h674
                                  · rcases p671_3 (m.d 1 2) (by simp) with h675 | h675
                                    · linarith only [h0, h675, hlam]
                                    · linarith only [h369, h675, hlam]
                                  · linarith only [h674, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 2) (by simp) with h679 | h679
                                  · rcases p671_3 (m.d 1 2) (by simp) with h680 | h680
                                    · linarith only [h0, h680, hlam]
                                    · linarith only [h370, h680, hlam]
                                  · linarith only [h679, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 2) (by simp) with h684 | h684
                                  · rcases p671_3 (m.d 1 2) (by simp) with h685 | h685
                                    · linarith only [h0, h685, hlam]
                                    · linarith only [h371, h685, hlam]
                                  · linarith only [h684, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h375, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 2) (by simp) with h692 | h692
                                  · rcases p671_3 (m.d 1 2) (by simp) with h693 | h693
                                    · rcases p671_3 (m.d 2 3) (by simp) with h694 | h694
                                      · linarith only [h369, h694, hlam]
                                      · linarith only [h374, h694, hlam]
                                    · linarith only [h693, hlam, p671_0]
                                  · linarith only [h5, h692, hlam]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 2) (by simp) with h699 | h699
                                  · rcases p671_3 (m.d 1 2) (by simp) with h700 | h700
                                    · rcases p671_3 (m.d 2 3) (by simp) with h701 | h701
                                      · linarith only [h369, h701, hlam]
                                      · linarith only [h375, h701, hlam]
                                    · linarith only [h700, hlam, p671_0]
                                  · linarith only [h6, h699, hlam]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h4, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h369, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h369, hc01, hc25, hlam, hphi, ht0b, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h5, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h370, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h374, hlam, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h376, hlam, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h6, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h371, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h375, hlam, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h371, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                              · rcases h2bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  rcases p721_3 (m.d 0 2) (by simp) with h724 | h724
                                  · rcases p721_3 (m.d 1 2) (by simp) with h725 | h725
                                    · linarith only [h0, h725, hlam]
                                    · linarith only [h369, h725, hlam]
                                  · linarith only [h724, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  rcases p721_3 (m.d 0 2) (by simp) with h729 | h729
                                  · rcases p721_3 (m.d 1 2) (by simp) with h730 | h730
                                    · linarith only [h0, h730, hlam]
                                    · linarith only [h370, h730, hlam]
                                  · linarith only [h729, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  rcases p721_3 (m.d 0 2) (by simp) with h734 | h734
                                  · rcases p721_3 (m.d 1 2) (by simp) with h735 | h735
                                    · linarith only [h0, h735, hlam]
                                    · linarith only [h371, h735, hlam]
                                  · linarith only [h734, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h0, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h0, h375, h378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  rcases p721_3 (m.d 0 2) (by simp) with h742 | h742
                                  · rcases p721_3 (m.d 1 2) (by simp) with h743 | h743
                                    · rcases p721_3 (m.d 2 3) (by simp) with h744 | h744
                                      · linarith only [h369, h744, hlam]
                                      · linarith only [h374, h744, hlam]
                                    · linarith only [h743, hlam, p721_0]
                                  · linarith only [h5, h742, hlam]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  rcases p721_3 (m.d 0 2) (by simp) with h749 | h749
                                  · rcases p721_3 (m.d 1 2) (by simp) with h750 | h750
                                    · rcases p721_3 (m.d 2 3) (by simp) with h751 | h751
                                      · linarith only [h369, h751, hlam]
                                      · linarith only [h375, h751, hlam]
                                    · linarith only [h750, hlam, p721_0]
                                  · linarith only [h6, h749, hlam]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h4, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h369, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h0, h369, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h0, h369, hc01, hc25, hlam, hphi, ht0b, ht5b, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h5, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h370, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h374, hlam, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h376, hlam, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h6, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h371, hlam, p721_0]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h375, hlam, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [h0, h371, h374, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                                · have p721_0 := h721c.1
                                  have p721_1 := h721c.2.1
                                  have p721_2 := h721c.2.2.1
                                  have p721_3 := h721c.2.2.2
                                  linarith only [hlam, p721_0]
                              · linarith only [h670, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h670, hc05, hlam, p380_1]
                              · linarith only [h670, h8, hlam, ht01, ht12, ht23, u3elo0]
                            · linarith only [h669, h9, hlam]
                        · linarith only [h666, h7, hlam]
                      · linarith only [h5, h665, hlam]
                    · linarith only [h2, h664, hlam]
                  · have p380_0 := h380c.1
                    have p380_1 := h380c.2.1
                    have p380_2 := h380c.2.2.1
                    have p380_3 := h380c.2.2.2
                    linarith only [hlam, p380_0]
            · linarith only [h375, h8, hc23, hlam, hphi, u3elo0]
          · linarith only [h374, h7, hc23, hlam, hphi, u3elo0]
        · linarith only [h373, h8, hc13, hlam, hphi, u3elo0]
      · linarith only [h369, h372, h7, hc23, hlam, hphi, u3elo0]
    · linarith only [h369, h371, h6, h8, hc23, hlam, hphi, u3elo0]
  · linarith only [h369, h370, h5, h7, hc23, hlam, hphi, u3elo0]

end R2N4
