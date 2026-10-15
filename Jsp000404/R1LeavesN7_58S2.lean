import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h10, h13, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h13, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h12, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h10, h11, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h10, h18, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                      · rcases h5bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h18, h4, h8, hc23, hlam, hphi, ht34, p22_1, u4elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h18, h4, h8, h9, hc23, hc25, hlam, hphi, ht01, ht0b, ht34, ht5b, p22_1, u1elo0, u4elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h18, h4, hc23, hlam, hphi, ht34, p22_1, u4elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h18, h4, h8, h9, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p22_1, u1elo0, u4elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h1, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, p22_1, u1elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h18, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22_1, u1elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p22_1, u1elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h2, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h6, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h18, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h3, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h8, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h3, hc03, hc25, hlam, hphi, ht0b, ht5b, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h8, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p22_1, u1elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h4, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h9, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h20, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h21, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                      · linarith only [h10, h21, h4, hc24, hlam, hphi, u4elo0]
                    · linarith only [h0, h10, h20, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h4, h9, hc14, hlam, hphi, u4elo0]
            · linarith only [h3, h4, h7, h8, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
            · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
              · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                · linarith only [h5, h52, h54, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                      · rcases h5bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p59_1, u4elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h4, h56, h58, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p59_1, u4elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h4, h58, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p59_1, u4elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p59_1, u4elo0]
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
                          linarith only [h56, h58, hc45, hlam, hphi, ht01, ht0b, ht5b, p59_1, u1elo4]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h52, h58, hc45, hlam, hphi, ht01, ht0b, ht5b, p59_1, u1elo2]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h52, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p59_1, u4elo3]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h6, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, h58, hc02, hc45, hlam, hphi, ht0b, ht5b, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h54, h56, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p59_1, u4elo2]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h3, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h52, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h56, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h4, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h53, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h57, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h58, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                      · linarith only [h58, h7, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h53, h57, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h52, h56, h7, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h4, h53, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
              · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                · linarith only [h3, h4, h5, h52, h90, hc34, hlam, hphi, u4elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h5, h52, h92, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h95 | h95
                      · rcases h5bigk with h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, h92, hc23, hlam, hphi, ht34, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, h52, hc13, hlam, hphi, ht34, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h1, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h92, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p96_1, u1elo4]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h52, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h89, hc45, hlam, hphi, ht01, ht0b, ht5b, p96_1, u1elo3]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h2, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h6, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h92, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h3, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h3, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p96_1, u4elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h89, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h94, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h95, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                      · linarith only [h94, h95, hc34, hlam, hphi, u4elo2]
                    · linarith only [h0, h89, h94, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h4, h89, hc14, hlam, hphi, u4elo0]
        · linarith only [h2, h4, h5, h6, hc23, hlam, hphi, ht34, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
        · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
          · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
            · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
              · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                      · rcases h5bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p134_1, u4elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p134_1, u4elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p134_1, u4elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p134_1, u4elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h1, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h131, hc35, hlam, hphi, ht01, ht0b, ht5b, p134_1, u1elo4]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h126, hc35, hlam, hphi, ht01, ht0b, ht5b, p134_1, u1elo1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h0, h129, hc45, hlam, hphi, ht01, ht0b, ht5b, p134_1, u1elo0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h2, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h126, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h126, hc45, hlam, hphi, ht01, ht0b, ht5b, p134_1, u1elo1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h3, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h128, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h131, hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h4, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h129, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h132, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [h133, hlam, p134_1]
                        · have p134_0 := h134c.1
                          have p134_1 := h134c.2.1
                          have p134_2 := h134c.2.2.1
                          have p134_3 := h134c.2.2.2
                          linarith only [hlam, p134_0]
                      · linarith only [h133, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h129, h132, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h128, h129, h131, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h130, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h129, h4, hc14, hlam, hphi, u4elo0]
            · linarith only [h127, h128, h3, h4, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
            · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                      · rcases h5bigk with h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p172_1, u4elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h169, h171, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p172_1, u4elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h171, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p172_1, u4elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p172_1, u4elo0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h1, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h169, h171, hc45, hlam, hphi, ht01, ht0b, ht5b, p172_1, u1elo4]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h126, h171, hc45, hlam, hphi, ht01, ht0b, ht5b, p172_1, u1elo1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h126, h127, h168, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p172_1, u4elo2]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h2, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h126, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h171, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h126, h127, h168, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p172_1, u4elo2]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h3, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h166, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h169, hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h4, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h167, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h170, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [h171, hlam, p172_1]
                        · have p172_0 := h172c.1
                          have p172_1 := h172c.2.1
                          have p172_2 := h172c.2.2.1
                          have p172_3 := h172c.2.2.2
                          linarith only [hlam, p172_0]
                      · linarith only [h127, h171, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h167, h170, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h126, h169, h3, h5, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h126, h168, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
              · linarith only [h167, h4, hc14, hlam, hphi, u4elo0]
            · linarith only [h126, h166, h5, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h204 | h204
          · rcases m.htr 1 3 5 (by decide) (by decide) with h205 | h205
            · rcases m.htr 1 4 5 (by decide) (by decide) with h206 | h206
              · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                      · rcases h5bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h126, h4, hc12, hlam, hphi, ht23, ht34, p211_1, u4elo0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p211_1, u4elo0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p211_1, u4elo0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p211_1, u4elo0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h1, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h126, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p211_1, u1elo4]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h0, h206, hc45, hlam, hphi, ht01, ht0b, ht5b, p211_1, u1elo0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h2, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p211_1, u4elo0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h3, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h205, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h208, hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h4, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h206, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h209, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [h210, hlam, p211_1]
                        · have p211_0 := h211c.1
                          have p211_1 := h211c.2.1
                          have p211_2 := h211c.2.2.1
                          have p211_3 := h211c.2.2.2
                          linarith only [hlam, p211_0]
                      · linarith only [h210, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h206, h209, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h205, h208, h5, hlam]
                · linarith only [h207, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h206, h4, hc14, hlam, hphi, u4elo0]
            · linarith only [h204, h205, h3, h4, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
            · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
              · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                      · rcases h5bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h126, h4, hc12, hlam, hphi, ht23, ht34, p249_1, u4elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h1, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h126, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h248, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo4]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h243, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo2]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, h248, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h3, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h243, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h246, hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h4, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h244, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h247, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [h248, hlam, p249_1]
                        · have p249_0 := h249c.1
                          have p249_1 := h249c.2.1
                          have p249_2 := h249c.2.2.1
                          have p249_3 := h249c.2.2.2
                          linarith only [hlam, p249_0]
                      · linarith only [h204, h248, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h244, h247, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h204, h243, h245, h246, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h245, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h244, h4, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h283 | h283
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                      · rcases h5bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [hlam, p285_0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h1, h243, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p285_1, u1elo0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h1, h243, h282, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p285_1, u1elo0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h1, h243, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p285_1, u1elo0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p285_1, u4elo0]
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
                          linarith only [h126, hlam, p285_0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h243, hlam, p285_0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p285_1, u1elo4]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h2, hlam, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [hlam, p285_0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h2, h243, h4, h5, hc12, hlam, hphi, ht23, ht34, p285_1, u4elo0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p285_1, u4elo0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h3, hlam, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h243, h5, hc12, hc35, hlam, hphi, ht23, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h282, hlam, p285_0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [hlam, p285_0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h2, h282, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p285_1, u4elo0]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h4, hlam, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h280, hlam, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h283, hlam, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [h284, hlam, p285_1]
                        · have p285_0 := h285c.1
                          have p285_1 := h285c.2.1
                          have p285_2 := h285c.2.2.1
                          have p285_3 := h285c.2.2.2
                          linarith only [hlam, p285_0]
                      · linarith only [h280, h284, hc34, hlam, hphi, u4elo1]
                    · linarith only [h0, h280, h283, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h204, h281, h282, h5, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h281, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h280, h4, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
      · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
        · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
          · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
            · rcases m.htr 1 4 5 (by decide) (by decide) with h320 | h320
              · linarith only [h320, h4, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                    · linarith only [h0, h318, h324, h4, hc34, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                      · linarith only [h0, h318, h326, h4, hlam]
                      · rcases h5bigk with h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h317, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h4, hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h1, hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p328_1, u1elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p328_1, u1elo0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h320, hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h2, hlam, p328_1]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h317, hlam, p328_1]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p328_1]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h324, hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h3, hlam, p328_1]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h319, hlam, p328_1]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h323, hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h326, hlam, p328_0]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [h323, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p328_1, u4elo4]
                        · have p328_0 := h328c.1
                          have p328_1 := h328c.2.1
                          have p328_2 := h328c.2.2.1
                          have p328_3 := h328c.2.2.2
                          linarith only [hlam, p328_0]
                  · linarith only [h1, h319, h322, h323, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h318, h322, h4, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h3, h318, h319, h4, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
            · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
              · linarith only [h0, h358, h4, hlam]
              · linarith only [h318, h357, h358, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h361 | h361
              · linarith only [h0, h361, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                · linarith only [h316, h318, h363, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                  · linarith only [h316, h357, h365, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                    · linarith only [h367, h4, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h369 | h369
                      · linarith only [h3, h316, h357, h369, h4, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h316, h318, h369, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h2, h316, h317, h4, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h373 | h373
        · rcases m.htr 1 3 4 (by decide) (by decide) with h374 | h374
          · rcases m.htr 1 3 5 (by decide) (by decide) with h375 | h375
            · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
              · linarith only [h0, h376, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                · rcases m.htr 2 3 5 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h380 | h380
                    · linarith only [h0, h374, h380, h4, hc34, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h382 | h382
                      · linarith only [h0, h374, h382, h4, hlam]
                      · rcases h5bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h373, h378, h380, h4, hc34, hlam, hphi, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h378, h380, h4, hc34, hlam, hphi, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h4, hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h1, hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h378, h380, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p384_1, u1elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h373, hc35, hlam, hphi, ht01, ht0b, ht5b, p384_1, u1elo1]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h376, hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h2, hlam, p384_1]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h373, hlam, p384_1]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h2, hc02, hc35, hlam, hphi, ht0b, ht5b, p384_1]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h380, hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h3, hlam, p384_1]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h375, hlam, p384_1]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h379, hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [h382, hlam, p384_0]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p384_1, u4elo4]
                        · have p384_0 := h384c.1
                          have p384_1 := h384c.2.1
                          have p384_2 := h384c.2.2.1
                          have p384_3 := h384c.2.2.2
                          linarith only [hlam, p384_0]
                  · linarith only [h3, h316, h379, h4, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h0, h316, h374, h378, h4, hc13, hlam, hphi, ht34, u4elo4]
            · linarith only [h3, h374, h375, h4, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h413 | h413
            · rcases m.htr 1 4 5 (by decide) (by decide) with h414 | h414
              · linarith only [h0, h4, h414, hlam]
              · linarith only [h316, h373, h374, h414, hlam]
            · linarith only [h316, h373, h413, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
          · rcases m.htr 1 3 5 (by decide) (by decide) with h419 | h419
            · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
              · linarith only [h0, h4, h420, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
                · rcases m.htr 2 3 5 (by decide) (by decide) with h423 | h423
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
                    · linarith only [h4, h424, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h426 | h426
                      · linarith only [h2, h373, h4, h418, h426, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases h5bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p428_1, u1elo0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h1, h373, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p428_1, u1elo0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p428_1, u1elo0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h4, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h1, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h373, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p428_1, u1elo4]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h420, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h2, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h2, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p428_1, u4elo4]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h424, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h3, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h419, hlam, p428_1]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h423, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h426, hlam, p428_0]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p428_1, u4elo4]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h420, hc14, hlam, hphi, p428_1, u4elo4]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [h373, hc12, hlam, hphi, ht23, ht34, p428_1, u4elo4]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p428_1, u4elo4]
                        · have p428_0 := h428c.1
                          have p428_1 := h428c.2.1
                          have p428_2 := h428c.2.2.1
                          have p428_3 := h428c.2.2.2
                          linarith only [hlam, p428_0]
                  · linarith only [h3, h316, h4, h423, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h316, h418, h422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h3, h4, h418, h419, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
            · rcases m.htr 1 4 5 (by decide) (by decide) with h458 | h458
              · linarith only [h0, h4, h458, hlam]
              · linarith only [h418, h457, h458, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
              · linarith only [h0, h4, h461, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h4, h465, hc04, hlam, hphi, u4elo2]
                    · linarith only [h316, h418, h463, h465, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h316, h418, h463, h464, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h316, h463, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
    · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
      · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
        · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
          · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
            · linarith only [h1, h3, h474, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
              · linarith only [h473, h474, h476, hlam]
              · linarith only [h470, h476, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h479 | h479
            · linarith only [h3, h473, h479, hc03, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
              · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
                · linarith only [h471, h473, h482, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h484 | h484
                  · linarith only [h3, h471, h484, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h486 | h486
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h487 | h487
                      · rcases h5bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, h479, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p488_1, u1elo0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, hc25, hlam, hphi, ht01, ht0b, ht5b, p488_1, u1elo0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h3, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p488_1, u1elo0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h1, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h486, hc45, hlam, hphi, ht01, ht0b, ht5b, p488_1, u1elo4]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h479, hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h0, h481, hc45, hlam, hphi, ht01, ht0b, ht5b, p488_1, u1elo0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h2, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h472, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h484, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h3, hc03, hc35, hlam, hphi, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h471, h479, hc23, hc35, hlam, hphi, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h484, hc23, hc35, hlam, hphi, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h487, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p488_1, u4elo3]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h470, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h481, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h486, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [h487, hlam, p488_1]
                        · have p488_0 := h488c.1
                          have p488_1 := h488c.2.1
                          have p488_2 := h488c.2.2.1
                          have p488_3 := h488c.2.2.2
                          linarith only [hlam, p488_0]
                      · linarith only [h486, h487, hc34, hlam, hphi, u4elo2]
                    · linarith only [h0, h481, h486, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h470, h481, hc14, hlam, hphi, u4elo0]
        · linarith only [h2, h470, h471, h472, hc23, hlam, hphi, ht34, u4elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h518 | h518
        · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
          · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
            · linarith only [h1, h3, h520, hlam]
            · linarith only [h471, h518, h520, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
            · linarith only [h3, h519, h523, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h471, h518, h523, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
          · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
            · linarith only [h1, h3, h527, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
              · linarith only [h526, h527, h529, hlam]
              · linarith only [h470, h529, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h532 | h532
            · linarith only [h3, h526, h532, hc03, hlam, hphi, ht34, u4elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h534 | h534
              · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                · rcases m.htr 2 3 5 (by decide) (by decide) with h536 | h536
                  · linarith only [h2, h3, h536, hlam]
                  · linarith only [h471, h526, h535, h536, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h471, h535, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h470, h534, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
      · rcases m.htr 1 2 5 (by decide) (by decide) with h542 | h542
        · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
          · rcases m.htr 1 3 5 (by decide) (by decide) with h544 | h544
            · linarith only [h1, h3, h544, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h546 | h546
              · linarith only [h470, h546, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h548 | h548
                · rcases m.htr 2 3 5 (by decide) (by decide) with h549 | h549
                  · linarith only [h541, h544, h549, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h551 | h551
                    · linarith only [h1, h470, h541, h544, h548, h551, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h553 | h553
                      · linarith only [h1, h470, h541, h544, h548, h553, hlam]
                      · linarith only [h541, h544, h548, h553, hc34, hlam, hphi, u4elo4]
                · linarith only [h0, h470, h543, h548, hc23, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
            · linarith only [h3, h543, h557, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
              · linarith only [h0, h470, h559, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                · linarith only [h0, h470, h541, h543, h561, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h563 | h563
                  · linarith only [h541, h557, h563, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
                    · linarith only [h470, h565, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                      · linarith only [h0, h470, h541, h543, h567, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h541, h543, h567, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h2, h470, h541, h542, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
        · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
          · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
            · linarith only [h1, h3, h573, hlam]
            · linarith only [h541, h571, h573, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
            · linarith only [h0, h3, h470, h572, h576, hc03, hlam, hphi, ht34, u4elo4]
            · linarith only [h541, h571, h576, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
          · rcases m.htr 1 3 5 (by decide) (by decide) with h580 | h580
            · linarith only [h1, h3, h580, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h582 | h582
              · linarith only [h0, h470, h582, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                  · linarith only [h2, h3, h585, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h587 | h587
                    · linarith only [h470, h587, hc04, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h589 | h589
                      · linarith only [h579, h587, h589, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h541, h585, h589, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h1, h541, h579, h580, h584, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h593 | h593
            · linarith only [h0, h3, h470, h579, h593, hc03, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h595 | h595
              · linarith only [h0, h470, h595, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h597 | h597
                · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
                  · linarith only [h2, h3, h598, hlam]
                  · linarith only [h541, h579, h597, h598, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h541, h597, hc12, hlam, hphi, ht23, ht34, u4elo3]

end R2N4
