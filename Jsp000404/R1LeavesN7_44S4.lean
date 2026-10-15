import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h13, h16, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h13, h15, h16, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h13, h15, h19, hlam]
                  · rcases h1bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h14, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h10, h12, h13, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h12, h13, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      rcases p21_3 (m.d 0 1) (by simp) with h26 | h26
                      · rcases p21_3 (m.d 1 2) (by simp) with h27 | h27
                        · linarith only [h0, h27, hlam]
                        · linarith only [h27, h9, hlam]
                      · linarith only [h26, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h10, h12, h13, h15, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, h12, h13, h15, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p21_1, u1ehi4]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h1, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h7, hlam, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h12, h13, h15, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p21_1, u1ehi4]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h2, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h8, hlam, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h10, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hc14, hlam, hphi, p21_1, u1ehi4]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h3, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h9, hlam, p21_1]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h11, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [h12, hlam, p21_0]
                    · have p21_0 := h21c.1
                      have p21_1 := h21c.2.1
                      have p21_2 := h21c.2.2.1
                      have p21_3 := h21c.2.2.2
                      linarith only [hlam, p21_0]
              · linarith only [h0, h11, h13, h14, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
              · linarith only [h1, h10, h13, h52, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                  · rcases h1bigk with h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, h52, h55, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, h52, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      rcases p56_3 (m.d 0 1) (by simp) with h60 | h60
                      · rcases p56_3 (m.d 1 2) (by simp) with h61 | h61
                        · linarith only [h0, h61, hlam]
                        · linarith only [h61, h8, hlam]
                      · linarith only [h60, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      rcases p56_3 (m.d 0 1) (by simp) with h65 | h65
                      · rcases p56_3 (m.d 1 2) (by simp) with h66 | h66
                        · linarith only [h0, h66, hlam]
                        · linarith only [h66, h9, hlam]
                      · linarith only [h65, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, h52, h55, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h1, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h7, hlam, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, hc13, hlam, hphi, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h2, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h8, hlam, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h10, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc14, hlam, hphi, p56_1, u1ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h3, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h9, hlam, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h11, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                  · linarith only [h0, h54, h55, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h10, h13, h54, h7, h91, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h12, h13, h7, h91, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
            · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
              · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                · linarith only [h12, h8, h96, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                  · linarith only [h12, h94, h98, hc23, hlam, hphi, ht12, u1ehi3]
                  · rcases h1bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h7, h95, h98, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 1) (by simp) with h103 | h103
                      · rcases p100_3 (m.d 1 2) (by simp) with h104 | h104
                        · linarith only [h0, h104, hlam]
                        · linarith only [h104, h7, hlam]
                      · linarith only [h103, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 1) (by simp) with h108 | h108
                      · rcases p100_3 (m.d 1 2) (by simp) with h109 | h109
                        · linarith only [h0, h109, hlam]
                        · linarith only [h109, h8, hlam]
                      · linarith only [h108, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 1) (by simp) with h113 | h113
                      · rcases p100_3 (m.d 1 2) (by simp) with h114 | h114
                        · linarith only [h0, h114, hlam]
                        · linarith only [h114, h9, hlam]
                      · linarith only [h113, hlam, p100_0]
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
                      linarith only [hc12, hlam, hphi, p100_1, u1ehi2]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h1, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h7, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hc13, hlam, hphi, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h2, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h8, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h10, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h12, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h3, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h9, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h11, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hc15, hlam, hphi, p100_1, u1ehi3]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
              · linarith only [h0, h11, h7, h94, h95, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
              · linarith only [h10, h12, h139, h2, h6, h94, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                · linarith only [h12, h141, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                  · linarith only [h10, h12, h143, hlam]
                  · rcases h1bigk with h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h10, h7, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h10, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      rcases p145_3 (m.d 0 1) (by simp) with h149 | h149
                      · rcases p145_3 (m.d 1 2) (by simp) with h150 | h150
                        · linarith only [h0, h150, hlam]
                        · linarith only [h150, h8, hlam]
                      · linarith only [h149, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      rcases p145_3 (m.d 0 1) (by simp) with h154 | h154
                      · rcases p145_3 (m.d 1 2) (by simp) with h155 | h155
                        · linarith only [h0, h155, hlam]
                        · linarith only [h155, h9, hlam]
                      · linarith only [h154, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h11, h143, h94, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p145_1, u1ehi4]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h1, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h7, hlam, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hc13, hlam, hphi, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p145_1, u1ehi4]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h2, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h8, hlam, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h10, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h12, hlam, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h3, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h9, hlam, p145_1]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [h11, hlam, p145_0]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hc15, hlam, hphi, p145_1, u1ehi3]
                    · have p145_0 := h145c.1
                      have p145_1 := h145c.2.1
                      have p145_2 := h145c.2.2.1
                      have p145_3 := h145c.2.2.2
                      linarith only [hlam, p145_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h179 | h179
          · linarith only [h10, h11, h179, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
            · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
              · linarith only [h10, h11, h182, hc23, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                · linarith only [h179, h181, h184, h7, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                  · linarith only [h0, h10, h11, h179, h186, h4, h5, hc01, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases h1bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h181, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 1) (by simp) with h191 | h191
                      · rcases p188_3 (m.d 1 2) (by simp) with h192 | h192
                        · linarith only [h0, h192, hlam]
                        · linarith only [h192, h7, hlam]
                      · linarith only [h191, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 1) (by simp) with h196 | h196
                      · rcases p188_3 (m.d 1 2) (by simp) with h197 | h197
                        · linarith only [h0, h197, hlam]
                        · linarith only [h197, h8, hlam]
                      · linarith only [h196, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 1) (by simp) with h201 | h201
                      · rcases p188_3 (m.d 1 2) (by simp) with h202 | h202
                        · linarith only [h0, h202, hlam]
                        · linarith only [h202, h9, hlam]
                      · linarith only [h201, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h10, hc12, hlam, hphi, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, h10, h11, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h1, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h7, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hc13, hlam, hphi, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h11, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h2, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h8, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h10, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h179, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h3, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h9, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hc15, hlam, hphi, p188_1, u1ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, h11, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p188_1, u1ehi3]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
            · linarith only [h0, h10, h11, h181, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
        · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
          · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
            · linarith only [h10, h227, h229, hc23, hlam, hphi, ht12, u1ehi4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h231 | h231
              · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                  · rcases h1bigk with h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h231, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p234_1]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      rcases p234_3 (m.d 0 1) (by simp) with h237 | h237
                      · rcases p234_3 (m.d 1 2) (by simp) with h238 | h238
                        · linarith only [h0, h238, hlam]
                        · linarith only [h238, h7, hlam]
                      · linarith only [h237, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      rcases p234_3 (m.d 0 1) (by simp) with h242 | h242
                      · rcases p234_3 (m.d 1 2) (by simp) with h243 | h243
                        · linarith only [h0, h243, hlam]
                        · linarith only [h243, h8, hlam]
                      · linarith only [h242, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      rcases p234_3 (m.d 0 1) (by simp) with h247 | h247
                      · rcases p234_3 (m.d 1 2) (by simp) with h248 | h248
                        · linarith only [h0, h248, hlam]
                        · linarith only [h248, h9, hlam]
                      · linarith only [h247, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h227, hc12, hlam, hphi, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, h10, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h1, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h7, hlam, p234_1]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h10, hlam, p234_1]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hc13, hlam, hphi, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h2, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h8, hlam, p234_1]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hc14, hlam, hphi, p234_1, u1ehi2]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p234_1, u1ehi4]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h3, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h9, hlam, p234_1]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h227, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [h228, hlam, p234_0]
                    · have p234_0 := h234c.1
                      have p234_1 := h234c.2.1
                      have p234_2 := h234c.2.2.1
                      have p234_3 := h234c.2.2.2
                      linarith only [hlam, p234_0]
                  · linarith only [h10, h233, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h2, h228, h229, h231, h232, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h10, h227, h231, hc23, hc34, hlam, hphi]
          · linarith only [h10, h227, h228, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
          · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
            · linarith only [h10, h277, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
              · linarith only [h227, h279, h7, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                  · rcases h1bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h281, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 1) (by simp) with h286 | h286
                      · rcases p283_3 (m.d 1 2) (by simp) with h287 | h287
                        · linarith only [h0, h287, hlam]
                        · linarith only [h287, h7, hlam]
                      · linarith only [h286, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 1) (by simp) with h291 | h291
                      · rcases p283_3 (m.d 1 2) (by simp) with h292 | h292
                        · linarith only [h0, h292, hlam]
                        · linarith only [h292, h8, hlam]
                      · linarith only [h291, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 1) (by simp) with h296 | h296
                      · rcases p283_3 (m.d 1 2) (by simp) with h297 | h297
                        · linarith only [h0, h297, hlam]
                        · linarith only [h297, h9, hlam]
                      · linarith only [h296, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc12, hlam, hphi, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h227, h276, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h1, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h7, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h10, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h227, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h2, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h8, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc14, hlam, hphi, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h227, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h3, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h9, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc15, hlam, hphi, p283_1, u1ehi2]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h276, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                  · linarith only [h10, h281, h282, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
                  · rcases h1bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h276, h277, h281, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      rcases p323_3 (m.d 0 1) (by simp) with h326 | h326
                      · rcases p323_3 (m.d 1 2) (by simp) with h327 | h327
                        · linarith only [h0, h327, hlam]
                        · linarith only [h327, h7, hlam]
                      · linarith only [h326, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h276, h277, h281, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      rcases p323_3 (m.d 0 1) (by simp) with h332 | h332
                      · rcases p323_3 (m.d 1 2) (by simp) with h333 | h333
                        · linarith only [h0, h333, hlam]
                        · linarith only [h333, h9, hlam]
                      · linarith only [h332, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc12, hlam, hphi, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, h276, h277, h281, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, h227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h1, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h7, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h10, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h227, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h2, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h8, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc14, hlam, hphi, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h0, h227, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h3, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h9, hlam, p323_1]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hc15, hlam, hphi, p323_1, u1ehi2]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [h276, hlam, p323_0]
                    · have p323_0 := h323c.1
                      have p323_1 := h323c.2.1
                      have p323_2 := h323c.2.2.1
                      have p323_3 := h323c.2.2.2
                      linarith only [hlam, p323_0]
                  · linarith only [h10, h2, h322, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
            · linarith only [h10, h358, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h360 | h360
              · linarith only [h10, h227, h360, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                · linarith only [h276, h362, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h364 | h364
                  · linarith only [h10, h276, h364, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                  · linarith only [h10, h364, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
      · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
        · linarith only [h368, h7, h9, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
          · linarith only [h370, h8, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
            · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
              · linarith only [h368, h373, h7, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h372, h373, h4, h5, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h367, h368, h372, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
        · linarith only [h367, h377, h8, h9, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
          · linarith only [h379, h8, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
            · linarith only [h367, h381, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h383 | h383
              · linarith only [h377, h381, h383, h8, hc12, hlam, hphi, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h385 | h385
                · linarith only [h0, h379, h383, h385, h4, h5, h8, h9, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h387 | h387
                  · linarith only [h381, h385, h387, h8, h9, hc23, hc34, hlam, hphi]
                  · linarith only [h367, h387, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
    · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
      · linarith only [h391, h7, h8, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
        · rcases m.htr 1 4 5 (by decide) (by decide) with h394 | h394
          · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
            · linarith only [h391, h395, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
              · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                · rcases m.htr 3 4 5 (by decide) (by decide) with h399 | h399
                  · rcases h1bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h397, h399, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p400_1]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      rcases p400_3 (m.d 0 1) (by simp) with h403 | h403
                      · rcases p400_3 (m.d 1 2) (by simp) with h404 | h404
                        · linarith only [h0, h404, hlam]
                        · linarith only [h404, h7, hlam]
                      · linarith only [h403, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h397, h399, h7, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p400_1]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      rcases p400_3 (m.d 0 1) (by simp) with h409 | h409
                      · rcases p400_3 (m.d 1 2) (by simp) with h410 | h410
                        · linarith only [h0, h410, hlam]
                        · linarith only [h390, h410, hlam]
                      · linarith only [h409, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h0, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h393, hc12, hlam, hphi, p400_1, u1ehi4]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h8, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h395, h8, hc34, hlam, hphi, ht12, ht23, p400_1, u1ehi4]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h1, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h7, hlam, p400_1]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h391, hlam, p400_1]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [hc13, hlam, hphi, p400_1, u1ehi4]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h2, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h2, h397, h399, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p400_1]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h2, h395, h397, h399, h7, h8, hc01, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p400_1, u1ehi2]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h2, h395, h397, h399, h7, h8, hc01, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p400_1, u1ehi4]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h3, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h390, hlam, p400_1]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h393, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [h394, hlam, p400_0]
                    · have p400_0 := h400c.1
                      have p400_1 := h400c.2.1
                      have p400_2 := h400c.2.2.1
                      have p400_3 := h400c.2.2.2
                      linarith only [hlam, p400_0]
                  · linarith only [h395, h399, h7, h8, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h3, h394, h397, h398, h7, h8, hc05, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h393, h395, h397, h7, h8, hc23, hc34, hlam, hphi]
          · linarith only [h393, h394, h7, h8, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h438 | h438
          · rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
            · linarith only [h391, h439, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h441 | h441
              · linarith only [h393, h441, h7, hc12, hlam, hphi, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h443 | h443
                · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
                  · rcases h1bigk with h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      rcases p445_3 (m.d 0 1) (by simp) with h447 | h447
                      · rcases p445_3 (m.d 1 2) (by simp) with h448 | h448
                        · linarith only [h448, hlam, p445_0]
                        · rcases p445_3 (m.d 1 3) (by simp) with h450 | h450
                          · linarith only [h1, h450, hlam]
                          · rcases p445_3 (m.d 1 4) (by simp) with h452 | h452
                            · linarith only [h2, h452, hlam]
                            · linarith only [h452, h8, hlam]
                      · linarith only [h447, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      rcases p445_3 (m.d 0 1) (by simp) with h456 | h456
                      · rcases p445_3 (m.d 1 2) (by simp) with h457 | h457
                        · linarith only [h0, h457, hlam]
                        · linarith only [h457, h7, hlam]
                      · linarith only [h456, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      rcases p445_3 (m.d 0 1) (by simp) with h461 | h461
                      · rcases p445_3 (m.d 1 2) (by simp) with h462 | h462
                        · linarith only [h0, h462, hlam]
                        · rcases p445_3 (m.d 1 3) (by simp) with h464 | h464
                          · linarith only [h1, h464, hlam]
                          · rcases p445_3 (m.d 1 4) (by simp) with h466 | h466
                            · linarith only [h466, hlam, p445_0]
                            · rcases p445_3 (m.d 1 5) (by simp) with h468 | h468
                              · linarith only [h3, h468, hlam]
                              · rcases h5bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 5) (by simp) with h472 | h472
                                  · rcases p470_3 (m.d 1 5) (by simp) with h473 | h473
                                    · linarith only [h3, h473, hlam]
                                    · rcases p470_3 (m.d 2 5) (by simp) with h475 | h475
                                      · linarith only [h390, h393, h475, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p445_1, p470_1, u1ehi2]
                                      · rcases p470_3 (m.d 3 5) (by simp) with h477 | h477
                                        · linarith only [h477, h5, hlam]
                                        · linarith only [h393, h477, hlam]
                                  · linarith only [h3, h472, hlam]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 5) (by simp) with h481 | h481
                                  · rcases p470_3 (m.d 1 5) (by simp) with h482 | h482
                                    · linarith only [h3, h482, hlam]
                                    · linarith only [h390, h482, hlam]
                                  · linarith only [h481, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h393, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p470_1, u1ehi2]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 5) (by simp) with h487 | h487
                                  · rcases p470_3 (m.d 1 5) (by simp) with h488 | h488
                                    · linarith only [h3, h488, hlam]
                                    · linarith only [h438, h488, hlam]
                                  · linarith only [h487, h6, hlam]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h3, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h390, h441, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h393, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h390, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p445_1, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h3, hc25, hlam, hphi, ht12, p470_1, u1ehi4]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h390, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h441, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h390, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p445_1, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h5, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h393, hc35, hlam, hphi, ht12, ht23, p470_1, u1ehi2]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 5) (by simp) with h504 | h504
                                  · rcases p470_3 (m.d 1 5) (by simp) with h505 | h505
                                    · linarith only [h393, h505, hlam]
                                    · linarith only [h390, h505, hlam]
                                  · linarith only [h5, h504, hlam, p470_1]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  rcases p470_3 (m.d 0 5) (by simp) with h510 | h510
                                  · rcases p470_3 (m.d 1 5) (by simp) with h511 | h511
                                    · linarith only [h393, h511, hlam]
                                    · linarith only [h438, h511, hlam]
                                  · linarith only [h510, h6, hlam]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h6, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h438, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h443, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [h444, hlam, p470_0]
                                · have p470_0 := h470c.1
                                  have p470_1 := h470c.2.1
                                  have p470_2 := h470c.2.2.1
                                  have p470_3 := h470c.2.2.2
                                  linarith only [hlam, p470_0]
                      · linarith only [h461, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      rcases p445_3 (m.d 0 1) (by simp) with h521 | h521
                      · rcases p445_3 (m.d 1 2) (by simp) with h522 | h522
                        · linarith only [h0, h522, hlam]
                        · linarith only [h390, h522, hlam]
                      · linarith only [h521, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hc12, hlam, hphi, p445_1, u1ehi2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h8, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h393, h439, h8, hc34, hlam, hphi, ht12, ht23, p445_1, u1ehi2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h1, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h7, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h391, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h393, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h2, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p445_1, u1ehi1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p445_1, u1ehi2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h2, h393, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p445_1, u1ehi2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h3, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h390, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h390, hc12, hlam, hphi, p445_1, u1ehi2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h438, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                  · linarith only [h439, h444, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h390, h438, h443, h8, hlam]
          · linarith only [h390, h438, h8, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
      · linarith only [h549, h7, h8, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h551 | h551
        · linarith only [h390, h551, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h553 | h553
          · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
            · linarith only [h549, h553, h554, h7, h8, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h556 | h556
              · linarith only [h551, h554, h556, h7, h8, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h558 | h558
                · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                  · rcases h1bigk with h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      rcases p560_3 (m.d 0 1) (by simp) with h562 | h562
                      · rcases p560_3 (m.d 1 2) (by simp) with h563 | h563
                        · linarith only [h563, hlam, p560_0]
                        · rcases p560_3 (m.d 1 3) (by simp) with h565 | h565
                          · linarith only [h1, h565, hlam]
                          · rcases p560_3 (m.d 1 4) (by simp) with h567 | h567
                            · linarith only [h2, h567, hlam]
                            · linarith only [h567, h8, hlam]
                      · linarith only [h562, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      rcases p560_3 (m.d 0 1) (by simp) with h571 | h571
                      · rcases p560_3 (m.d 1 2) (by simp) with h572 | h572
                        · linarith only [h0, h572, hlam]
                        · linarith only [h572, h7, hlam]
                      · linarith only [h571, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      rcases p560_3 (m.d 0 1) (by simp) with h576 | h576
                      · rcases p560_3 (m.d 1 2) (by simp) with h577 | h577
                        · linarith only [h0, h577, hlam]
                        · rcases p560_3 (m.d 1 3) (by simp) with h579 | h579
                          · linarith only [h1, h579, hlam]
                          · rcases p560_3 (m.d 1 4) (by simp) with h581 | h581
                            · linarith only [h581, hlam, p560_0]
                            · rcases p560_3 (m.d 1 5) (by simp) with h583 | h583
                              · linarith only [h3, h583, hlam]
                              · rcases h5bigk with h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  rcases p585_3 (m.d 0 5) (by simp) with h587 | h587
                                  · rcases p585_3 (m.d 1 5) (by simp) with h588 | h588
                                    · linarith only [h3, h588, hlam]
                                    · rcases p585_3 (m.d 2 5) (by simp) with h590 | h590
                                      · linarith only [h0, h390, h4, h5, h556, h590, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p585_1]
                                      · linarith only [h390, h590, hlam]
                                  · linarith only [h3, h587, hlam]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h390, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p585_1, u1ehi2]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h4, h5, h551, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p585_1, u1ehi2]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  rcases p585_3 (m.d 0 5) (by simp) with h596 | h596
                                  · rcases p585_3 (m.d 1 5) (by simp) with h597 | h597
                                    · linarith only [h3, h597, hlam]
                                    · linarith only [h553, h597, hlam]
                                  · linarith only [h596, h6, hlam]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h3, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h390, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h551, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h553, hc01, hc45, hlam, hphi, ht0b, ht5b, p560_1, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h3, h558, hc24, hlam, hphi, ht12, p585_1, u1ehi4]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h554, h558, hc34, hlam, hphi, ht12, ht23, p585_1, u1ehi4]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h556, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  rcases p585_3 (m.d 0 5) (by simp) with h610 | h610
                                  · rcases p585_3 (m.d 1 5) (by simp) with h611 | h611
                                    · linarith only [h390, h611, hlam]
                                    · linarith only [h553, h611, hlam]
                                  · linarith only [h6, h610, hlam]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h5, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h390, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p585_1, u1ehi2]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h390, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p585_1, u1ehi2]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  rcases p585_3 (m.d 0 5) (by simp) with h619 | h619
                                  · rcases p585_3 (m.d 1 5) (by simp) with h620 | h620
                                    · linarith only [h551, h620, hlam]
                                    · linarith only [h553, h620, hlam]
                                  · linarith only [h6, h619, hlam]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h6, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h553, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h558, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h559, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                      · linarith only [h576, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      rcases p560_3 (m.d 0 1) (by simp) with h630 | h630
                      · rcases p560_3 (m.d 1 2) (by simp) with h631 | h631
                        · linarith only [h0, h631, hlam]
                        · rcases p560_3 (m.d 1 3) (by simp) with h633 | h633
                          · linarith only [h1, h633, hlam]
                          · rcases p560_3 (m.d 1 4) (by simp) with h635 | h635
                            · linarith only [h2, h635, hlam]
                            · linarith only [h553, h635, hlam]
                      · linarith only [h630, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h0, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hc12, hlam, hphi, p560_1, u1ehi2]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h8, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h390, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h1, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h7, hlam, p560_1]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h549, hlam, p560_1]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h551, hlam, p560_1]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h2, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hc14, hlam, hphi, p560_1, u1ehi1]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p560_1, u1ehi2]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p560_1, u1ehi4]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h3, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h7, hc15, hlam, hphi, p560_1, u1ehi2]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h0, h4, h5, h551, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p560_1, u1ehi2]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [h553, hlam, p560_0]
                    · have p560_0 := h560c.1
                      have p560_1 := h560c.2.1
                      have p560_2 := h560c.2.2.1
                      have p560_3 := h560c.2.2.2
                      linarith only [hlam, p560_0]
                  · linarith only [h2, h554, h559, h6, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · linarith only [h553, h558, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h661 | h661
            · linarith only [h549, h661, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h663 | h663
              · linarith only [h2, h553, h6, h663, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h665 | h665
                · linarith only [h553, h661, h665, h7, h8, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h2, h6, h665, h7, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]

end R2N4
