import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_14_H_I_L_0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h11, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h10, h4, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h15, h8, h9, hlam]
                    · linarith only [h15, h4, hc24, hlam, hphi, u4elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                      · rcases h2bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h18, h20, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h18, h20, hc01, hc45, hlam, hphi, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h18, h20, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          rcases p21_3 (m.d 0 2) (by simp) with h26 | h26
                          · rcases p21_3 (m.d 1 2) (by simp) with h27 | h27
                            · linarith only [h0, h27, hlam]
                            · linarith only [h27, h7, hlam]
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
                          linarith only [h18, h20, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h18, h20, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h1, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h5, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h8, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p21_1, u4elo2]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h2, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h6, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, p21_1, u4elo2]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h18, h20, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h3, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h7, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h18, hlam, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                      · linarith only [h20, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h19, h4, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                      · rcases h2bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          rcases p55_3 (m.d 0 2) (by simp) with h58 | h58
                          · rcases p55_3 (m.d 1 2) (by simp) with h59 | h59
                            · linarith only [h0, h59, hlam]
                            · linarith only [h5, h59, hlam]
                          · linarith only [h58, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, h53, hc01, hc45, hlam, hphi, ht0b, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          rcases p55_3 (m.d 0 2) (by simp) with h64 | h64
                          · rcases p55_3 (m.d 1 2) (by simp) with h65 | h65
                            · linarith only [h0, h65, hlam]
                            · linarith only [h65, h7, hlam]
                          · linarith only [h64, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, h53, hc01, hc45, hlam, hphi, ht0b, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, h18, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h1, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h5, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h8, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h18, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h2, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h6, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, p55_1, u4elo2]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, h18, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h3, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h7, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p55_1]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [h53, hlam, p55_0]
                        · have p55_0 := h55c.1
                          have p55_1 := h55c.2.1
                          have p55_2 := h55c.2.2.1
                          have p55_3 := h55c.2.2.2
                          linarith only [hlam, p55_0]
                      · linarith only [h4, h54, h8, hc24, hlam, hphi, u4elo0]
                    · linarith only [h4, h53, h8, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h3, h4, h5, h7, hc23, hlam, hphi, ht34, u4elo0]
            · linarith only [h5, h6, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
            · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
              · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                    · linarith only [h0, h1, h5, h93, h97, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h97, hc24, hlam, hphi, u4elo0]
                  · linarith only [h5, h94, h96, hlam]
                · linarith only [h5, h95, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h3, h4, h93, h94, hc24, hlam, hphi, u4elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                      · rcases h2bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h0, h103, h105, h107, hc01, hc45, hlam, hphi, ht0b, ht5b, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h0, h103, h104, h105, h107, h93, hc01, hc45, hlam, hphi, ht0b, ht5b, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h0, h103, h105, h107, h93, hc01, hc45, hlam, hphi, ht0b, ht5b, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          rcases p108_3 (m.d 0 2) (by simp) with h113 | h113
                          · rcases p108_3 (m.d 1 2) (by simp) with h114 | h114
                            · linarith only [h0, h114, hlam]
                            · linarith only [h103, h114, hlam]
                          · linarith only [h113, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h0, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h5, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h93, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h105, h107, h2, h93, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p108_1, u4elo0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h1, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h0, h1, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h0, h1, h105, h107, hc01, hc45, hlam, hphi, ht0b, ht5b, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h2, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h103, h105, h107, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p108_1, u4elo0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h104, hlam, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h105, h107, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p108_1, u4elo0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h3, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h103, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h105, hlam, p108_1]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [h106, hlam, p108_0]
                        · have p108_0 := h108c.1
                          have p108_1 := h108c.2.1
                          have p108_2 := h108c.2.2.1
                          have p108_3 := h108c.2.2.2
                          linarith only [hlam, p108_0]
                      · linarith only [h107, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h106, h4, h93, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h103, h104, h105, h93, hlam]
                · linarith only [h103, h104, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                · rcases m.htr 2 3 5 (by decide) (by decide) with h143 | h143
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h145 | h145
                      · rcases h2bigk with h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          rcases p146_3 (m.d 0 2) (by simp) with h148 | h148
                          · rcases p146_3 (m.d 1 2) (by simp) with h149 | h149
                            · linarith only [h0, h149, hlam]
                            · rcases p146_3 (m.d 2 3) (by simp) with h151 | h151
                              · linarith only [h1, h151, hlam]
                              · linarith only [h151, h5, hlam]
                          · linarith only [h0, h148, hlam]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h142, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, h93, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, h103, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h5, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h93, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h103, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h1, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, h1, h93, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h0, h1, h103, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h2, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h142, hlam, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h103, h2, hc12, hlam, hphi, ht23, ht34, p146_1, u4elo0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h3, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h143, hlam, p146_1]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [h144, hlam, p146_0]
                        · have p146_0 := h146c.1
                          have p146_1 := h146c.2.1
                          have p146_2 := h146c.2.2.1
                          have p146_3 := h146c.2.2.2
                          linarith only [hlam, p146_0]
                      · linarith only [h145, h4, hc34, hlam, hphi, u4elo0]
                    · linarith only [h144, h4, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                    · linarith only [h142, h143, h180, hlam]
                    · linarith only [h180, h4, hc24, hlam, hphi, u4elo0]
                · linarith only [h142, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
          · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
            · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
              · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h189 | h189
                    · linarith only [h189, h2, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                      · linarith only [h184, h187, h191, h4, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, h184, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, h188, hc01, hc35, hlam, hphi, ht0b, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          rcases p193_3 (m.d 0 2) (by simp) with h197 | h197
                          · rcases p193_3 (m.d 1 2) (by simp) with h198 | h198
                            · linarith only [h0, h198, hlam]
                            · linarith only [h185, h198, hlam]
                          · linarith only [h197, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          rcases p193_3 (m.d 0 2) (by simp) with h202 | h202
                          · rcases p193_3 (m.d 1 2) (by simp) with h203 | h203
                            · linarith only [h0, h203, hlam]
                            · linarith only [h186, h203, hlam]
                          · linarith only [h202, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h188, h191, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, h187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h1, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h184, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, h1, h187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, h184, hc01, hc25, hlam, hphi, ht0b, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h2, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h185, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h187, hlam, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h189, hlam, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h3, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h186, hlam, p193_0]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h188, hlam, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [h0, h187, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p193_1]
                        · have p193_0 := h193c.1
                          have p193_1 := h193c.2.1
                          have p193_2 := h193c.2.2.1
                          have p193_3 := h193c.2.2.2
                          linarith only [hlam, p193_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                    · linarith only [h2, h227, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                      · linarith only [h187, h188, h229, h3, h4, hlam]
                      · linarith only [h187, h188, h229, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                    · linarith only [h2, h233, h4, hlam]
                    · linarith only [h187, h232, h233, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                    · linarith only [h2, h236, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                      · linarith only [h238, h4, hc04, hlam, hphi, u4elo3]
                      · linarith only [h187, h238, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h184, h186, h3, h4, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h184, h185, h2, hc23, hlam, hphi, ht34, u4elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
            · rcases m.htr 1 2 5 (by decide) (by decide) with h244 | h244
              · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                    · linarith only [h184, h243, h247, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                      · linarith only [h2, h245, h249, h4, hlam]
                      · rcases h2bigk with h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, h244, hc01, hc25, hlam, hphi, ht0b, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, h184, h244, h246, hc01, hc35, hlam, hphi, ht0b, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          rcases p251_3 (m.d 0 2) (by simp) with h255 | h255
                          · rcases p251_3 (m.d 1 2) (by simp) with h256 | h256
                            · linarith only [h0, h256, hlam]
                            · linarith only [h243, h256, hlam]
                          · linarith only [h255, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          rcases p251_3 (m.d 0 2) (by simp) with h260 | h260
                          · rcases p251_3 (m.d 1 2) (by simp) with h261 | h261
                            · linarith only [h0, h261, hlam]
                            · linarith only [h244, h261, hlam]
                          · linarith only [h260, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h184, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h184, h245, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, h1, h184, h245, h247, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h1, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, h1, h245, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h0, h1, h245, h247, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h2, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h243, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h245, hlam, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h247, hlam, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h3, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h244, hlam, p251_0]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h246, hlam, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [h244, h245, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p251_1]
                        · have p251_0 := h251c.1
                          have p251_1 := h251c.2.1
                          have p251_2 := h251c.2.2.1
                          have p251_3 := h251c.2.2.2
                          linarith only [hlam, p251_0]
                  · linarith only [h184, h244, h246, hlam]
                · linarith only [h184, h245, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h243, h244, h3, h4, hc24, hlam, hphi, u4elo4]
            · linarith only [h2, h243, h4, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
        · linarith only [h2, h289, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
          · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
            · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
              · linarith only [h0, h293, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                · linarith only [h0, h289, h291, h295, h3, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h0, h292, h295, h297, h3, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h0, h289, h292, h299, h3, hlam]
                    · linarith only [h0, h292, h295, h299, h3, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h291, h292, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h1, h291, h3, hc12, hc25, hlam, hphi]
    · linarith only [h1, h2, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h305 | h305
    · rcases m.htr 0 2 5 (by decide) (by decide) with h306 | h306
      · rcases m.htr 0 4 5 (by decide) (by decide) with h307 | h307
        · rcases m.htr 1 2 3 (by decide) (by decide) with h308 | h308
          · linarith only [h0, h1, h305, h308, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
            · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
              · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                · rcases m.htr 2 3 5 (by decide) (by decide) with h313 | h313
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h315 | h315
                      · rcases h2bigk with h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h310, h312, h315, hc02, hc45, hlam, hphi, ht0b, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h1, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h1, h312, h315, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h1, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h0, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h308, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h312, h315, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h0, h1, h313, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h312, h315, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          rcases p316_3 (m.d 0 2) (by simp) with h331 | h331
                          · linarith only [h1, h331, hlam]
                          · linarith only [h306, h331, hlam]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h305, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h310, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h312, hlam, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h0, h310, h313, h315, hc02, hc45, hlam, hphi, ht0b, ht5b, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h306, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h311, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h313, hlam, p316_1]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [h314, hlam, p316_0]
                        · have p316_0 := h316c.1
                          have p316_1 := h316c.2.1
                          have p316_2 := h316c.2.2.1
                          have p316_3 := h316c.2.2.2
                          linarith only [hlam, p316_0]
                      · linarith only [h307, h315, hc34, hlam, hphi, u4elo0]
                    · linarith only [h307, h314, hc24, hlam, hphi, u4elo0]
                  · linarith only [h1, h306, h313, hlam]
                · linarith only [h1, h312, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h1, h306, h310, h311, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h1, h305, h310, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
          · linarith only [h0, h1, h306, h350, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
            · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
              · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h356 | h356
                    · linarith only [h0, h1, h307, h352, h356, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                      · linarith only [h305, h307, h354, h358, hlam]
                      · rcases h2bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h1, hc12, hc23, hlam, hphi, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h1, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h1, h354, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h1, h354, h356, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h0, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h350, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h0, h354, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h0, h1, h354, h356, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          rcases p360_3 (m.d 0 2) (by simp) with h374 | h374
                          · linarith only [h1, h374, hlam]
                          · linarith only [h305, h374, hlam]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          rcases p360_3 (m.d 0 2) (by simp) with h377 | h377
                          · linarith only [h1, h377, hlam]
                          · linarith only [h306, h377, hlam]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h305, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h352, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h354, hlam, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h356, hlam, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h306, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h353, hlam, p360_0]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h355, hlam, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [h0, h353, h354, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                        · have p360_0 := h360c.1
                          have p360_1 := h360c.2.1
                          have p360_2 := h360c.2.2.1
                          have p360_3 := h360c.2.2.2
                          linarith only [hlam, p360_0]
                  · linarith only [h0, h1, h353, h355, hlam]
                · linarith only [h1, h354, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h1, h306, h352, h353, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h1, h305, h352, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
        · linarith only [h305, h306, h394, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
          · linarith only [h0, h1, h396, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h398 | h398
            · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
              · linarith only [h0, h306, h399, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h403 | h403
                    · linarith only [h0, h306, h394, h398, h402, h403, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h306, h398, h403, hc24, hlam, hphi, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                    · linarith only [h394, h406, hc04, hlam, hphi, u4elo2]
                    · linarith only [h1, h305, h401, h402, h406, hc34, hlam, hphi, u4elo4]
                · linarith only [h0, h1, h398, h401, hc24, hlam, hphi, u4elo3]
            · linarith only [h1, h305, h398, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h411 | h411
      · rcases m.htr 0 4 5 (by decide) (by decide) with h412 | h412
        · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
          · linarith only [h0, h1, h305, h413, hc03, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h415 | h415
            · linarith only [h0, h305, h415, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h417 | h417
              · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                      · rcases h2bigk with h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h305, hc12, hlam, hphi, ht23, ht34, p422_1, u4elo2]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h1, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h305, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h305, h419, h421, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p422_1, u4elo2]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h0, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h413, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h415, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h0, h419, h421, hc01, hc45, hlam, hphi, ht0b, ht5b, p422_1]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p422_1]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p422_1]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h0, h305, h417, h419, h421, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p422_1]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          rcases p422_3 (m.d 0 2) (by simp) with h437 | h437
                          · linarith only [h1, h437, hlam]
                          · linarith only [h411, h437, hlam]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h0, h417, h419, h421, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p422_1, u4elo2]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h417, h419, h421, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p422_1, u4elo2]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h418, hlam, p422_1]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h419, h421, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p422_1, u4elo2]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h411, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h417, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h419, hlam, p422_1]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [h420, hlam, p422_0]
                        · have p422_0 := h422c.1
                          have p422_1 := h422c.2.1
                          have p422_2 := h422c.2.2.1
                          have p422_3 := h422c.2.2.2
                          linarith only [hlam, p422_0]
                      · linarith only [h412, h421, hc34, hlam, hphi, u4elo0]
                    · linarith only [h305, h411, h412, h420, hlam]
                  · linarith only [h0, h305, h413, h417, h419, hc13, hlam, hphi, ht34, u4elo2]
                · linarith only [h1, h418, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h1, h411, h417, hc12, hc23, hlam, hphi]
        · linarith only [h305, h411, h412, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
        · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
          · linarith only [h0, h1, h457, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
            · linarith only [h0, h305, h459, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
              · linarith only [h0, h411, h461, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h466 | h466
                      · rcases h2bigk with h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h411, h465, hc12, hlam, hphi, ht23, ht34, p467_1, u4elo2]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h1, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h305, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h411, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h0, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h457, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h459, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h461, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h0, h305, hc12, hc23, hlam, hphi, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h0, h411, hc12, hc23, hlam, hphi, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, p467_1, u4elo2]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, p467_1, u4elo2]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h463, hlam, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h0, h411, hc12, hlam, hphi, ht23, ht34, p467_1, u4elo2]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h464, hlam, p467_1]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [h465, hlam, p467_0]
                        · have p467_0 := h467c.1
                          have p467_1 := h467c.2.1
                          have p467_2 := h467c.2.2.1
                          have p467_3 := h467c.2.2.2
                          linarith only [hlam, p467_0]
                      · linarith only [h456, h466, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h305, h465, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                    · linarith only [h463, h464, h495, hlam]
                    · linarith only [h305, h456, h495, hlam]
                · linarith only [h0, h1, h463, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
          · linarith only [h0, h1, h499, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
            · linarith only [h0, h305, h501, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
              · linarith only [h0, h411, h503, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                · rcases m.htr 2 3 5 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h507 | h507
                    · linarith only [h305, h456, h507, hc02, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h0, h305, h507, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h510 | h510
                    · linarith only [h0, h305, h456, h505, h506, h510, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h305, h510, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h0, h1, h505, hc12, hlam, hphi, ht23, ht34, u4elo3]

end R2N4
