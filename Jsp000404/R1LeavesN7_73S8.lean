import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_14_M_LI_L_0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h10, h4, h7, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h13, h9, hc14, hlam, hphi, u4elo2]
                    · rcases h1bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h8, hc35, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        rcases p15_3 (m.d 0 1) (by simp) with h19 | h19
                        · rcases p15_3 (m.d 1 2) (by simp) with h20 | h20
                          · linarith only [h0, h20, hlam]
                          · linarith only [h20, h5, hlam]
                        · linarith only [h19, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        rcases p15_3 (m.d 0 1) (by simp) with h24 | h24
                        · rcases p15_3 (m.d 1 2) (by simp) with h25 | h25
                          · linarith only [h0, h25, hlam]
                          · linarith only [h25, h6, hlam]
                        · linarith only [h24, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h0, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1, u1elo1]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h0, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h1, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h4, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h1, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h0, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h2, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h5, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h7, hlam, p15_1]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h9, hlam, p15_1]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h3, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h6, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h8, hlam, p15_0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [h3, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1, u1elo0]
                      · have p15_0 := h15c.1
                        have p15_1 := h15c.2.1
                        have p15_2 := h15c.2.2.1
                        have p15_3 := h15c.2.2.2
                        linarith only [hlam, p15_0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, h7, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h49, h51, hc14, hlam, hphi, u4elo2]
                    · rcases h1bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        rcases p53_3 (m.d 0 1) (by simp) with h57 | h57
                        · rcases p53_3 (m.d 1 2) (by simp) with h58 | h58
                          · linarith only [h0, h58, hlam]
                          · linarith only [h5, h58, hlam]
                        · linarith only [h57, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h7, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h0, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p53_1, u1elo1]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h0, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h1, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h4, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h1, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h8, hlam, p53_1]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h2, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h5, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h7, hlam, p53_1]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h49, hlam, p53_1]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h3, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h6, hlam, p53_0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h49, hc13, hlam, hphi, ht34, p53_1, u4elo4]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [h0, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p53_1, u1elo0]
                      · have p53_0 := h53c.1
                        have p53_1 := h53c.2.1
                        have p53_2 := h53c.2.2.1
                        have p53_3 := h53c.2.2.2
                        linarith only [hlam, p53_0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h0, h5, h85, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h84, h85, hc24, hlam, hphi, u4elo1]
                  · linarith only [h7, h83, h84, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h5, h90, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h89, h90, hc24, hlam, hphi, u4elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h7, h89, h93, hc13, hlam, hphi, ht34, u4elo2]
                    · rcases h1bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 1) (by simp) with h98 | h98
                        · rcases p95_3 (m.d 1 2) (by simp) with h99 | h99
                          · linarith only [h0, h99, hlam]
                          · linarith only [h4, h99, hlam]
                        · linarith only [h98, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 1) (by simp) with h103 | h103
                        · rcases p95_3 (m.d 1 2) (by simp) with h104 | h104
                          · linarith only [h0, h104, hlam]
                          · linarith only [h104, h5, hlam]
                        · linarith only [h103, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 1) (by simp) with h108 | h108
                        · rcases p95_3 (m.d 1 2) (by simp) with h109 | h109
                          · linarith only [h0, h109, hlam]
                          · linarith only [h109, h6, hlam]
                        · linarith only [h108, hlam, p95_0]
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
                        linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h0, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p95_1, u1elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h1, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h4, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h7, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h83, hlam, p95_1]
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
                        linarith only [h4, h89, hc23, hlam, hphi, ht34, p95_1, u4elo4]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h89, hlam, p95_1]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h3, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h6, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p95_1, u1elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h0, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p95_1, u1elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
              · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                · linarith only [h134, h4, h6, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                  · linarith only [h136, h5, h6, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                    · linarith only [h136, h138, hc14, hlam, hphi, u4elo2]
                    · linarith only [h138, h4, h6, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h141 | h141
                · linarith only [h133, h141, h4, h6, hc23, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                  · linarith only [h143, h5, h6, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h145 | h145
                    · linarith only [h143, h145, hc14, hlam, hphi, u4elo2]
                    · linarith only [h145, h4, h6, hc23, hlam, hphi, ht34, u4elo4]
          · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
          · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
            · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
              · rcases m.htr 1 3 5 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                    · linarith only [h0, h149, h154, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h153, h154, hc24, hlam, hphi, u4elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                    · linarith only [h153, h157, hc14, hlam, hphi, u4elo2]
                    · rcases h1bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h150, hc25, hlam, hphi, ht01, ht0b, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h152, hc35, hlam, hphi, ht01, ht0b, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        rcases p159_3 (m.d 0 1) (by simp) with h163 | h163
                        · rcases p159_3 (m.d 1 2) (by simp) with h164 | h164
                          · linarith only [h0, h164, hlam]
                          · linarith only [h149, h164, hlam]
                        · linarith only [h163, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        rcases p159_3 (m.d 0 1) (by simp) with h168 | h168
                        · rcases p159_3 (m.d 1 2) (by simp) with h169 | h169
                          · linarith only [h0, h169, hlam]
                          · linarith only [h150, h169, hlam]
                        · linarith only [h168, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h4, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, h149, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h1, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h1, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h1, h149, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h1, h150, h157, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h2, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h149, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h151, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h153, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h3, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h150, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h152, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h149, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p159_1, u1elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                · linarith only [h150, h152, h4, hlam]
              · linarith only [h149, h151, h4, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
              · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h149, h150, h197, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                    · linarith only [h149, h197, h199, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h149, h150, h199, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                  · linarith only [h149, h196, h202, h4, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                    · linarith only [h202, h204, hc14, hlam, hphi, u4elo2]
                    · linarith only [h149, h150, h204, hc24, hlam, hphi, u4elo4]
              · linarith only [h149, h195, h4, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
            · rcases m.htr 1 3 4 (by decide) (by decide) with h209 | h209
              · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h212 | h212
                    · rcases h1bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h208, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h149, h208, h209, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h149, h208, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        rcases p213_3 (m.d 0 1) (by simp) with h218 | h218
                        · rcases p213_3 (m.d 1 2) (by simp) with h219 | h219
                          · linarith only [h0, h219, hlam]
                          · linarith only [h208, h219, hlam]
                        · linarith only [h218, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h0, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h4, hlam, p213_1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h149, hlam, p213_1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h149, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p213_1, u4elo2]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h1, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h208, hc25, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo2]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h1, h149, h208, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h1, h208, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h2, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h208, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo3]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h209, hlam, p213_1]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h1, h208, h209, h212, hc45, hlam, hphi, ht01, ht0b, ht5b, p213_1, u1elo0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h3, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h208, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h210, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [h211, hlam, p213_0]
                      · have p213_0 := h213c.1
                        have p213_1 := h213c.2.1
                        have p213_2 := h213c.2.2.1
                        have p213_3 := h213c.2.2.2
                        linarith only [hlam, p213_0]
                    · linarith only [h149, h212, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h149, h208, h211, hlam]
                · linarith only [h149, h208, h209, h210, hc34, hlam, hphi, u4elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                    · rcases h1bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h208, h248, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h208, h248, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h208, h209, h248, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        rcases p249_3 (m.d 0 1) (by simp) with h254 | h254
                        · rcases p249_3 (m.d 1 2) (by simp) with h255 | h255
                          · linarith only [h0, h255, hlam]
                          · linarith only [h208, h255, hlam]
                        · linarith only [h254, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h0, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h4, hlam, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h149, hlam, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h209, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo3]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h1, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h209, hc12, hlam, hphi, ht23, ht34, p249_1, u4elo3]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h209, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h208, h209, h248, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo3]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h2, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h208, h248, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo3]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p249_1, u1elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h2, h208, h248, hc45, hlam, hphi, ht01, ht0b, ht5b, p249_1, u1elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h3, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h208, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h246, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h247, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                    · linarith only [h149, h248, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h149, h208, h247, hlam]
                · linarith only [h208, h246, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
              · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
                · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                    · rcases h1bigk with h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        rcases p286_3 (m.d 0 1) (by simp) with h288 | h288
                        · rcases p286_3 (m.d 1 2) (by simp) with h289 | h289
                          · linarith only [h289, hlam, p286_0]
                          · rcases p286_3 (m.d 1 3) (by simp) with h291 | h291
                            · linarith only [h1, h291, hlam]
                            · linarith only [h291, h4, hlam]
                        · linarith only [h288, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h282, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h284, hc45, hlam, hphi, ht01, ht0b, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        rcases p286_3 (m.d 0 1) (by simp) with h297 | h297
                        · rcases p286_3 (m.d 1 2) (by simp) with h298 | h298
                          · linarith only [h0, h298, hlam]
                          · rcases p286_3 (m.d 1 3) (by simp) with h300 | h300
                            · linarith only [h1, h300, hlam]
                            · linarith only [h283, h300, hlam]
                        · linarith only [h297, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h0, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h4, hlam, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h149, hlam, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h208, hlam, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h1, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h1, h284, hc45, hlam, hphi, ht01, ht0b, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h2, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, p286_1, u4elo1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h282, hlam, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h1, h208, h282, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h3, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p286_1, u1elo0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h283, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h284, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                    · linarith only [h149, h285, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                    · linarith only [h284, h325, hc14, hlam, hphi, u4elo2]
                    · linarith only [h149, h325, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                  · linarith only [h282, h283, h328, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                    · linarith only [h328, h330, hc14, hlam, hphi, u4elo2]
                    · linarith only [h149, h330, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h333 | h333
                · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                    · rcases h1bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        rcases p336_3 (m.d 0 1) (by simp) with h338 | h338
                        · rcases p336_3 (m.d 1 2) (by simp) with h339 | h339
                          · linarith only [h339, hlam, p336_0]
                          · rcases p336_3 (m.d 1 3) (by simp) with h341 | h341
                            · linarith only [h1, h341, hlam]
                            · linarith only [h341, h4, hlam]
                        · linarith only [h338, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h333, hc35, hlam, hphi, ht01, ht0b, ht5b, p336_1, u1elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h282, h333, hc35, hlam, hphi, ht01, ht0b, ht5b, p336_1, u1elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        rcases p336_3 (m.d 0 1) (by simp) with h347 | h347
                        · rcases p336_3 (m.d 1 2) (by simp) with h348 | h348
                          · linarith only [h0, h348, hlam]
                          · rcases p336_3 (m.d 1 3) (by simp) with h350 | h350
                            · linarith only [h1, h350, hlam]
                            · linarith only [h333, h350, hlam]
                        · linarith only [h347, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h0, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h4, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h149, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h208, hlam, p336_1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h1, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h282, hc12, hlam, hphi, ht23, ht34, p336_1, u4elo1]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h282, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h282, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p336_1, u4elo3]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p336_1, u1elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p336_1, u1elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h2, h208, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p336_1, u1elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p336_1, u1elo0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h333, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [h334, hlam, p336_0]
                      · have p336_0 := h336c.1
                        have p336_1 := h336c.2.1
                        have p336_2 := h336c.2.2.1
                        have p336_3 := h336c.2.2.2
                        linarith only [hlam, p336_0]
                    · linarith only [h149, h334, h335, hlam]
                  · linarith only [h282, h333, h334, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
                    · rcases h1bigk with h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        rcases p378_3 (m.d 0 1) (by simp) with h380 | h380
                        · rcases p378_3 (m.d 1 2) (by simp) with h381 | h381
                          · linarith only [h381, hlam, p378_0]
                          · rcases p378_3 (m.d 1 3) (by simp) with h383 | h383
                            · linarith only [h1, h383, hlam]
                            · linarith only [h383, h4, hlam]
                        · linarith only [h380, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        rcases p378_3 (m.d 0 1) (by simp) with h387 | h387
                        · rcases p378_3 (m.d 1 2) (by simp) with h388 | h388
                          · linarith only [h0, h388, hlam]
                          · rcases p378_3 (m.d 1 3) (by simp) with h390 | h390
                            · linarith only [h390, hlam, p378_0]
                            · rcases p378_3 (m.d 1 4) (by simp) with h392 | h392
                              · linarith only [h2, h392, hlam]
                              · linarith only [h282, h392, hlam]
                        · linarith only [h387, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h376, hc45, hlam, hphi, ht01, ht0b, ht5b, p378_1, u1elo0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        rcases p378_3 (m.d 0 1) (by simp) with h397 | h397
                        · rcases p378_3 (m.d 1 2) (by simp) with h398 | h398
                          · linarith only [h0, h398, hlam]
                          · rcases p378_3 (m.d 1 3) (by simp) with h400 | h400
                            · linarith only [h1, h400, hlam]
                            · rcases p378_3 (m.d 1 4) (by simp) with h402 | h402
                              · linarith only [h2, h402, hlam]
                              · linarith only [h376, h402, hlam]
                        · linarith only [h397, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h0, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h4, hlam, p378_1]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h149, hlam, p378_1]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h208, hlam, p378_1]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h1, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h333, hc12, hc35, hlam, hphi, ht23, p378_1]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h282, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h333, hlam, p378_1]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h2, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, p378_1, u4elo1]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p378_1, u1elo0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p378_1, u1elo0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h3, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p378_1, u1elo0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p378_1, u1elo0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [h376, hlam, p378_0]
                      · have p378_0 := h378c.1
                        have p378_1 := h378c.2.1
                        have p378_2 := h378c.2.2.1
                        have p378_3 := h378c.2.2.2
                        linarith only [hlam, p378_0]
                    · linarith only [h149, h377, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                    · linarith only [h376, h427, hc14, hlam, hphi, u4elo2]
                    · linarith only [h149, h427, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
        · linarith only [h0, h3, h430, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
          · linarith only [h1, h3, h430, h432, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
            · linarith only [h1, h3, h430, h434, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
              · linarith only [h1, h3, h436, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h438 | h438
                · linarith only [h2, h3, h436, h438, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h440 | h440
                  · linarith only [h2, h3, h440, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                  · linarith only [h2, h3, h430, h436, h440, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h444 | h444
    · rcases m.htr 0 1 5 (by decide) (by decide) with h445 | h445
      · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
        · linarith only [h0, h1, h446, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
          · linarith only [h0, h1, h448, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
            · linarith only [h1, h444, h448, h450, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
              · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
                  · linarith only [h1, h444, h454, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                    · linarith only [h448, h454, h456, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h448, h456, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h0, h1, h453, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h444, h448, h452, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
        · linarith only [h0, h1, h461, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
          · linarith only [h0, h1, h463, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h465 | h465
            · linarith only [h1, h444, h463, h465, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
              · rcases m.htr 1 3 5 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 4 5 (by decide) (by decide) with h469 | h469
                  · linarith only [h444, h445, h468, h469, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · linarith only [h444, h445, h463, h469, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h1, h444, h463, h468, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h444, h463, h467, hc12, hc34, hlam, hphi, ht23]
    · linarith only [h0, h444, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
