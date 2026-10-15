import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_0_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h1, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · linarith only [h1, h3, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h1, h10, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · linarith only [h1, h10, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
            · linarith only [h1, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
            · linarith only [h0, h16, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
              · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h15, h19, h3, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h15, h18, h21, h3, hlam]
                  · rcases h4bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, h18, h3, hc45, hlam, hphi, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h18, h3, hc45, hlam, hphi, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h3, hc45, hlam, hphi, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h3, hlam, p23_0]
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
                      linarith only [h0, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h0, h3, hc45, hlam, hphi, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h16, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h1, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h19, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h2, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h18, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23_1, u2elo2, u4ehi1]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h18, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h21, hlam, p23_0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hc45, hlam, hphi, p23_1, u4ehi0]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h15, hc45, hlam, hphi, p23_1, u4ehi2]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [h18, hc45, hlam, hphi, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hc45, hlam, hphi, p23_1, u4ehi3]
                    · have p23_0 := h23c.1
                      have p23_1 := h23c.2.1
                      have p23_2 := h23c.2.2.1
                      have p23_3 := h23c.2.2.2
                      linarith only [hlam, p23_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                · linarith only [h1, h49, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                  · linarith only [h2, h3, h51, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases h4bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h15, h3, hc45, hlam, hphi, p53_1, u4ehi2]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h3, hc45, hlam, hphi, p53_1, u4ehi2]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h3, hc45, hlam, hphi, p53_1, u4ehi3]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h3, hlam, p53_0]
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
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p53_1, u4ehi2]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h0, h18, h3, hc23, hc45, hlam, hphi, ht34, p53_1]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h16, hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h1, hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h15, hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h18, hlam, p53_1]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h49, hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h2, hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p53_1, u4ehi1]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h2, h3, hc45, hlam, hphi, p53_1, u4ehi2]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h51, hlam, p53_0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [hc45, hlam, hphi, p53_1, u4ehi0]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h15, hc45, hlam, hphi, p53_1, u4ehi2]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [hc45, hlam, hphi, p53_1, u4ehi2]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [h18, hc23, hc45, hlam, hphi, ht34, p53_1]
                    · have p53_0 := h53c.1
                      have p53_1 := h53c.2.1
                      have p53_2 := h53c.2.2.1
                      have p53_3 := h53c.2.2.2
                      linarith only [hlam, p53_0]
          · linarith only [h1, h15, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
        · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
          · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
            · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
              · linarith only [h0, h2, h82, h83, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                · linarith only [h1, h85, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · linarith only [h0, h82, h85, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h1, h80, h82, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
          · linarith only [h1, h81, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
          · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
            · linarith only [h0, h80, h91, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
              · linarith only [h0, h2, h90, h93, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                · linarith only [h0, h80, h90, h95, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                  · rcases h4bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h80, h97, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u4ehi1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h80, h97, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u4ehi2]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h2, hlam, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h80, hlam, p98_0]
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
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p98_1, u4ehi2]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, h80, h97, hlam, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h91, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h1, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h90, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h93, hlam, p98_1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h95, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 4) (by simp) with h114 | h114
                      · linarith only [h114, h2, hlam]
                      · rcases p98_3 (m.d 1 4) (by simp) with h116 | h116
                        · linarith only [h0, h116, h80, h97, hlam]
                        · rcases p98_3 (m.d 2 4) (by simp) with h118 | h118
                          · linarith only [h118, h93, hlam]
                          · rcases p98_3 (m.d 3 4) (by simp) with h120 | h120
                            · rcases p98_3 (m.d 4 5) (by simp) with h121 | h121
                              · linarith only [h121, h97, hlam]
                              · linarith only [h121, h80, hlam]
                            · linarith only [h120, h2, hlam]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 4) (by simp) with h125 | h125
                      · linarith only [h125, h2, hlam]
                      · linarith only [h0, h125, hlam]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      rcases p98_3 (m.d 0 4) (by simp) with h128 | h128
                      · linarith only [h128, h2, hlam]
                      · linarith only [h1, h128, hlam]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u4ehi0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p98_1, u4ehi1]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h90, hc45, hlam, hphi, p98_1, u4ehi2]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hc45, hlam, hphi, p98_1, u4ehi2]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [h97, hlam, p98_0]
                    · have p98_0 := h98c.1
                      have p98_1 := h98c.2.1
                      have p98_2 := h98c.2.2.1
                      have p98_3 := h98c.2.2.2
                      linarith only [hlam, p98_0]
                  · rcases h4bigk with h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h1, h90, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p138_1, u2elo0, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p138_1, u2elo0, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h2, hlam, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h80, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h0, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p138_1, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h0, h2, hlam, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h91, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h1, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h90, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h93, hlam, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h95, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h97, hc45, hlam, hphi, p138_1, u4ehi0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h90, h97, hc45, hlam, hphi, p138_1, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h97, hc45, hlam, hphi, p138_1, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h97, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h0, h90, hc45, hlam, hphi, p138_1, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h90, hc45, hlam, hphi, p138_1, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hc45, hlam, hphi, p138_1, u4ehi2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hc45, hlam, hphi, p138_1, u4ehi3]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
          · linarith only [h1, h90, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h165 | h165
      · rcases m.htr 0 4 5 (by decide) (by decide) with h166 | h166
        · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
          · linarith only [h1, h167, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
            · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
              · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                · rcases m.htr 3 4 5 (by decide) (by decide) with h172 | h172
                  · linarith only [h170, h172, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h0, h1, h169, h172, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · linarith only [h0, h1, h169, h171, hlam]
              · linarith only [h1, h165, h170, hlam]
            · linarith only [h1, h166, h169, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
          · linarith only [h1, h178, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
            · linarith only [h0, h166, h180, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
              · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                · linarith only [h165, h166, h183, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                  · linarith only [h1, h183, h185, hc02, hc34, hlam, hphi, ht23]
                  · rcases h4bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p187_1, u2elo3, u4ehi1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, hlam, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p187_1, u2elo3, u4ehi3]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h166, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h178, hlam, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi3]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h180, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h183, hc45, hlam, hphi, p187_1, u4ehi0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h183, hc45, hlam, hphi, p187_1, u4ehi1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h183, hc45, hlam, hphi, p187_1, u4ehi3]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h183, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h165, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h165, hc03, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h182, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h185, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p187_1, u4ehi1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hc45, hlam, hphi, p187_1, u4ehi1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hc45, hlam, hphi, p187_1, u4ehi3]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
              · linarith only [h1, h165, h182, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h214 | h214
        · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
          · linarith only [h1, h214, h215, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
            · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
              · linarith only [h0, h165, h217, h218, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                  · rcases h4bigk with h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h217, hc04, hlam, hphi, ht0b, ht45, ht5b, p222_1, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h1, hlam, p222_1]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h165, hlam, p222_1]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p222_1, u2elo3, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h0, hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h215, hlam, p222_1]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h0, h1, h218, hc01, hlam, hphi, ht0b, ht45, ht5b, p222_1, u4ehi0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p222_1, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h214, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p222_1, u2elo3, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p222_1, u2elo3, u4ehi1]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h218, hlam, p222_1]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p222_1, u2elo3, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h0, h217, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p222_1, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h217, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p222_1, u4ehi4]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h1, hc02, hc34, hlam, hphi, ht23, p222_1]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      rcases p222_3 (m.d 0 4) (by simp) with h242 | h242
                      · linarith only [h165, h242, hlam]
                      · linarith only [h214, h242, hlam]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h214, hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h217, hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h220, hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [h221, hlam, p222_0]
                    · have p222_0 := h222c.1
                      have p222_1 := h222c.2.1
                      have p222_2 := h222c.2.2.1
                      have p222_3 := h222c.2.2.2
                      linarith only [hlam, p222_0]
                  · linarith only [h0, h1, h217, h221, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · linarith only [h0, h1, h217, h220, hlam]
            · linarith only [h1, h214, h217, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
          · linarith only [h1, h253, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
            · linarith only [h0, h214, h255, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h257 | h257
              · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                · linarith only [h0, h214, h258, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                  · linarith only [h1, h257, h258, h260, hc02, hlam, hphi, u2elo2]
                  · rcases h4bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h165, h257, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p262_1, u2elo2, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h1, hlam, p262_1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h165, hlam, p262_1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h214, hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h253, hlam, p262_1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, h165, hc01, hlam, hphi, ht0b, ht45, ht5b, p262_1, u4ehi0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h255, hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p262_1, u2elo3, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h258, hc45, hlam, hphi, p262_1, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, h165, h258, hc45, hlam, hphi, p262_1, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h258, hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, h257, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p262_1, u2elo2, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h257, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p262_1, u2elo2, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h257, hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h260, hlam, p262_0]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p262_1, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [hc45, hlam, hphi, p262_1, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h253, hc12, hc45, hlam, hphi, ht23, ht34, p262_1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [h0, h165, hc45, hlam, hphi, p262_1, u4ehi1]
                    · have p262_0 := h262c.1
                      have p262_1 := h262c.2.1
                      have p262_2 := h262c.2.2.1
                      have p262_3 := h262c.2.2.2
                      linarith only [hlam, p262_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h288 | h288
                · linarith only [h0, h214, h288, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h1, h288, h290, hc02, hc34, hlam, hphi, ht23]
                  · rcases h4bigk with h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p292_1, u2elo3, u4ehi1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h1, hlam, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h165, hlam, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h214, hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h0, hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h253, hlam, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h0, h1, h257, hc01, hlam, hphi, ht0b, ht45, ht5b, p292_1, u4ehi0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h255, hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p292_1, u2elo3, u4ehi0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h257, h290, hc45, hlam, hphi, p292_1, u4ehi1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h257, hlam, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h288, hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h0, h290, hc45, hlam, hphi, p292_1, u4ehi1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h290, hc45, hlam, hphi, p292_1, u4ehi1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h1, h290, hc02, hc45, hlam, hphi, ht23, ht34, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h290, hlam, p292_0]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p292_1, u4ehi1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hc45, hlam, hphi, p292_1, u4ehi1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [h257, hc23, hc45, hlam, hphi, ht34, p292_1]
                    · have p292_0 := h292c.1
                      have p292_1 := h292c.2.1
                      have p292_2 := h292c.2.2.1
                      have p292_3 := h292c.2.2.2
                      linarith only [hlam, p292_0]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
    · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
      · rcases m.htr 0 4 5 (by decide) (by decide) with h320 | h320
        · rcases m.htr 1 2 4 (by decide) (by decide) with h321 | h321
          · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
            · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
              · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                · linarith only [h318, h324, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · linarith only [h0, h320, h321, h324, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                · linarith only [h318, h327, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · linarith only [h0, h320, h321, h327, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
            · linarith only [h0, h320, h322, hlam]
          · linarith only [h318, h321, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
          · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
            · linarith only [h318, h320, h332, h333, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
              · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                · linarith only [h333, h336, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                  · linarith only [h0, h319, h333, h338, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases h4bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h0, hlam, p340_1]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h0, h333, h335, hc45, hlam, hphi, p340_1, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h0, h333, hc45, hlam, hphi, p340_1, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h320, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h333, hc45, hlam, hphi, p340_1, u4ehi0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h333, h335, hc45, hlam, hphi, p340_1, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h333, hc45, hlam, hphi, p340_1, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h333, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h318, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h332, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p340_1, u2elo3, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h336, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h319, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p340_1]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h335, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h338, hlam, p340_0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hc45, hlam, hphi, p340_1, u4ehi0]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p340_1]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [h335, hc45, hlam, hphi, p340_1, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hc45, hlam, hphi, p340_1, u4ehi3]
                    · have p340_0 := h340c.1
                      have p340_1 := h340c.2.1
                      have p340_2 := h340c.2.2.1
                      have p340_3 := h340c.2.2.2
                      linarith only [hlam, p340_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                · linarith only [h318, h366, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h0, h333, h368, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h4bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h0, hlam, p370_1]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h0, h333, hc45, hlam, hphi, p370_1, u4ehi2]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h0, h333, hc45, hlam, hphi, p370_1, u4ehi3]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h320, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h333, hc45, hlam, hphi, p370_1, u4ehi0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h333, hc45, hlam, hphi, p370_1, u4ehi2]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h333, h335, hc23, hc45, hlam, hphi, ht34, p370_1]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h333, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h318, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h332, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h335, hlam, p370_1]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h366, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h319, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p370_1]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h318, h319, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1, u2elo0, u4ehi2]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h368, hlam, p370_0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hc45, hlam, hphi, p370_1, u4ehi0]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p370_1]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hc45, hlam, hphi, p370_1, u4ehi2]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [h335, hc23, hc45, hlam, hphi, ht34, p370_1]
                    · have p370_0 := h370c.1
                      have p370_1 := h370c.2.1
                      have p370_2 := h370c.2.2.1
                      have p370_3 := h370c.2.2.2
                      linarith only [hlam, p370_0]
          · linarith only [h318, h332, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
        · rcases m.htr 1 2 4 (by decide) (by decide) with h398 | h398
          · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
            · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
              · linarith only [h319, h397, h400, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h402 | h402
                · linarith only [h318, h402, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                · linarith only [h0, h397, h398, h402, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
            · linarith only [h0, h397, h399, hlam]
          · linarith only [h318, h398, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
          · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
            · linarith only [h318, h397, h407, h408, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
              · linarith only [h318, h319, h410, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                · linarith only [h408, h412, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                  · linarith only [h0, h408, h414, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h4bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, h408, hc45, hlam, hphi, p416_1, u4ehi2]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h319, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h397, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h408, hc45, hlam, hphi, p416_1, u4ehi0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h408, hc45, hlam, hphi, p416_1, u4ehi2]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h408, hc45, hlam, hphi, p416_1, u4ehi3]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h408, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h318, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h407, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h410, hlam, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h412, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h318, h414, hc45, hlam, hphi, p416_1, u4ehi2]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h414, hc45, hlam, hphi, p416_1, u4ehi1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h414, hc45, hlam, hphi, p416_1, u4ehi2]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h414, hlam, p416_0]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h318, hc45, hlam, hphi, p416_1, u4ehi2]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p416_1]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hc45, hlam, hphi, p416_1, u4ehi2]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hc45, hlam, hphi, p416_1, u4ehi3]
                    · have p416_0 := h416c.1
                      have p416_1 := h416c.2.1
                      have p416_2 := h416c.2.2.1
                      have p416_3 := h416c.2.2.2
                      linarith only [hlam, p416_0]
          · linarith only [h318, h407, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h443 | h443
      · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
        · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
          · linarith only [h318, h445, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h447 | h447
            · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
              · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                  · linarith only [h448, h450, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h0, h444, h445, h450, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · linarith only [h0, h444, h445, h449, hlam]
              · linarith only [h0, h443, h445, h448, hlam]
            · linarith only [h0, h444, h447, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
          · linarith only [h318, h456, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h458 | h458
            · linarith only [h444, h456, h458, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
              · rcases m.htr 2 4 5 (by decide) (by decide) with h461 | h461
                · linarith only [h458, h460, h461, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h463 | h463
                  · linarith only [h443, h456, h461, h463, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h4bigk with h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h0, hlam, p465_1]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h318, hlam, p465_1]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h0, h456, h461, hc45, hlam, hphi, p465_1, u4ehi3]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h444, hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h456, h461, hc45, hlam, hphi, p465_1, u4ehi0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h456, hlam, p465_1]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h456, h461, hc45, hlam, hphi, p465_1, u4ehi3]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h458, hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h443, h461, hc45, hlam, hphi, p465_1, u4ehi3]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h461, hc45, hlam, hphi, p465_1, u4ehi1]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h461, hc45, hlam, hphi, p465_1, u4ehi3]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h461, hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h443, hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p465_1]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h460, hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h463, hlam, p465_0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hc45, hlam, hphi, p465_1, u4ehi0]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p465_1]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hc45, hlam, hphi, p465_1, u4ehi2]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hc45, hlam, hphi, p465_1, u4ehi3]
                    · have p465_0 := h465c.1
                      have p465_1 := h465c.2.1
                      have p465_2 := h465c.2.2.1
                      have p465_3 := h465c.2.2.2
                      linarith only [hlam, p465_0]
              · linarith only [h0, h443, h456, h460, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h492 | h492
        · rcases m.htr 1 2 4 (by decide) (by decide) with h493 | h493
          · linarith only [h318, h492, h493, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
            · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
              · linarith only [h443, h492, h496, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h498 | h498
                · rcases m.htr 3 4 5 (by decide) (by decide) with h499 | h499
                  · rcases h4bigk with h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h0, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h318, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h443, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h0, h493, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo3, u4ehi4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo3, u4ehi0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, h496, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo3, u4ehi4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h492, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo3, u4ehi4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo3, u4ehi1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h496, hlam, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo3, u4ehi4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h492, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p500_1, u4ehi4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h0, h492, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p500_1, u4ehi4]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h493, hc12, hc34, hlam, hphi, ht23, p500_1]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      rcases p500_3 (m.d 0 4) (by simp) with h520 | h520
                      · linarith only [h443, h520, hlam]
                      · linarith only [h492, h520, hlam]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h492, hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h495, hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h498, hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [h499, hlam, p500_0]
                    · have p500_0 := h500c.1
                      have p500_1 := h500c.2.1
                      have p500_2 := h500c.2.2.1
                      have p500_3 := h500c.2.2.2
                      linarith only [hlam, p500_0]
                  · linarith only [h0, h492, h493, h499, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · linarith only [h0, h492, h493, h498, hlam]
            · linarith only [h0, h492, h495, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
          · linarith only [h318, h531, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h533 | h533
            · linarith only [h492, h531, h533, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
              · rcases m.htr 2 4 5 (by decide) (by decide) with h536 | h536
                · linarith only [h533, h535, h536, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h538 | h538
                  · linarith only [h531, h536, h538, hc12, hc34, hlam, hphi, ht23]
                  · rcases h4bigk with h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h0, hlam, p540_1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h318, hlam, p540_1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h443, hlam, p540_1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h492, hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h531, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p540_1, u2elo3, u4ehi0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h531, hlam, p540_1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h531, h536, hc45, hlam, hphi, p540_1, u4ehi3]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h533, hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h536, hc45, hlam, hphi, p540_1, u4ehi0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h536, hc45, hlam, hphi, p540_1, u4ehi1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h443, h536, hc03, hc45, hlam, hphi, ht34, p540_1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h536, hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h535, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p540_1, u2elo2, u4ehi0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h0, h535, hc01, hlam, hphi, ht12, p540_1, u2elo2]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h535, hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h538, hlam, p540_0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hc45, hlam, hphi, p540_1, u4ehi0]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p540_1]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hc45, hlam, hphi, p540_1, u4ehi2]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hc45, hlam, hphi, p540_1, u4ehi3]
                    · have p540_0 := h540c.1
                      have p540_1 := h540c.2.1
                      have p540_2 := h540c.2.2.1
                      have p540_3 := h540c.2.2.2
                      linarith only [hlam, p540_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h566 | h566
                · linarith only [h492, h566, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h568 | h568
                  · linarith only [h0, h531, h566, h568, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h4bigk with h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h0, hlam, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h318, hlam, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h443, hlam, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h492, hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h531, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p570_1, u2elo3, u4ehi0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h531, hlam, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h531, h535, hlam, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h533, hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h535, h568, hc45, hlam, hphi, p570_1, u4ehi0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h535, h568, hc45, hlam, hphi, p570_1, u4ehi1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h535, hlam, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h566, hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h568, hc45, hlam, hphi, p570_1, u4ehi0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h0, h568, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h568, hc45, hlam, hphi, p570_1, u4ehi2]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h568, hlam, p570_0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [hc45, hlam, hphi, p570_1, u4ehi0]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h0, h531, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [h535, hc23, hc45, hlam, hphi, ht34, p570_1]
                    · have p570_0 := h570c.1
                      have p570_1 := h570c.2.1
                      have p570_2 := h570c.2.2.1
                      have p570_3 := h570c.2.2.2
                      linarith only [hlam, p570_0]

end R2N4
