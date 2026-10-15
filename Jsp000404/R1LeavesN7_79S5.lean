import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_23_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
            · linarith only [h0, h3, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
            · linarith only [h0, h3, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
        · linarith only [h2, h3, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
        · linarith only [h12, h2, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h12, h15, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h12, h14, h17, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h12, h14, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                  · rcases h3bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h14, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1, u0elo2, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h12, h21, hc34, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h2, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h12, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h0, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1, u0elo0, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h0, h12, h21, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1, u0elo0, u3ehi0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h15, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h1, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h14, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h17, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h19, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h0, hc34, hlam, hphi, p22_1, u3ehi1]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h14, hc34, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hc34, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h0, h12, h14, hc34, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h0, h14, hc35, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h14, hc35, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hc35, hlam, hphi, p22_1, u3ehi2]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [h21, hlam, p22_0]
                    · have p22_0 := h22c.1
                      have p22_1 := h22c.2.1
                      have p22_2 := h22c.2.2.1
                      have p22_3 := h22c.2.2.2
                      linarith only [hlam, p22_0]
                  · linarith only [h0, h14, h2, h21, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
            · linarith only [h0, h49, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
              · linarith only [h1, h2, h51, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                · linarith only [h1, h2, h53, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                  · rcases h3bigk with h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, h55, hc34, hlam, hphi, p56_1, u3ehi1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, h55, hc34, hlam, hphi, p56_1, u3ehi2]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h2, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, hlam, p56_0]
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
                      linarith only [h14, hlam, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h12, h55, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p56_1, u3ehi0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h49, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h1, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p56_1, u0elo2, u3ehi1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h51, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h53, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc34, hlam, hphi, p56_1, u3ehi0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc34, hlam, hphi, p56_1, u3ehi1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc34, hlam, hphi, p56_1, u3ehi2]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc34, hlam, hphi, p56_1, u3ehi4]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h1, hc35, hlam, hphi, p56_1, u3ehi2]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hc35, hlam, hphi, p56_1, u3ehi1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h14, hc12, hc35, hlam, hphi, ht23, p56_1]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [h55, hlam, p56_0]
                    · have p56_0 := h56c.1
                      have p56_1 := h56c.2.1
                      have p56_2 := h56c.2.2.1
                      have p56_3 := h56c.2.2.2
                      linarith only [hlam, p56_0]
                  · linarith only [h1, h14, h2, h55, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
      · rcases m.htr 0 3 5 (by decide) (by decide) with h84 | h84
        · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
          · linarith only [h0, h1, h83, h85, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
            · linarith only [h0, h87, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
            · linarith only [h84, h87, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · linarith only [h83, h84, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
        · linarith only [h83, h91, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
          · linarith only [h0, h1, h93, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
            · linarith only [h0, h91, h95, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
              · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                  · rcases h3bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h91, h93, h97, h99, hc12, hc23, hlam, hphi, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h1, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h83, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h91, hlam, p100_0]
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
                      linarith only [h93, hlam, p100_1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h91, h99, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u3ehi0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h95, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 3) (by simp) with h111 | h111
                      · linarith only [h1, h111, hlam]
                      · rcases p100_3 (m.d 1 3) (by simp) with h113 | h113
                        · linarith only [h113, h93, hlam]
                        · rcases p100_3 (m.d 2 3) (by simp) with h115 | h115
                          · rcases p100_3 (m.d 3 4) (by simp) with h116 | h116
                            · linarith only [h116, h97, hlam]
                            · linarith only [h116, h83, hlam]
                          · linarith only [h1, h115, hlam]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      rcases p100_3 (m.d 0 3) (by simp) with h120 | h120
                      · linarith only [h1, h120, hlam]
                      · linarith only [h0, h120, hlam]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h91, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h91, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, hc34, hlam, hphi, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h97, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, h91, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h0, hc35, hlam, hphi, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hc35, hlam, hphi, p100_1, u3ehi1]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h98, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [h99, hlam, p100_0]
                    · have p100_0 := h100c.1
                      have p100_1 := h100c.2.1
                      have p100_2 := h100c.2.2.1
                      have p100_3 := h100c.2.2.2
                      linarith only [hlam, p100_0]
                  · linarith only [h0, h83, h99, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h0, h83, h97, h98, hc35, hlam, hphi, u3ehi1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                · linarith only [h138, h97, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                  · rcases h3bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, u0elo2, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h1, hlam, p141_1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h83, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h91, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h0, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h93, hlam, p141_1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h1, h138, h140, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p141_1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h95, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h138, h140, hc34, hlam, hphi, p141_1, u3ehi0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h138, h140, hc34, hlam, hphi, p141_1, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h97, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h138, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h0, hc34, hlam, hphi, p141_1, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hc34, hlam, hphi, p141_1, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h1, hc02, hc34, hlam, hphi, ht23, p141_1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hc34, hlam, hphi, p141_1, u3ehi4]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h0, hc35, hlam, hphi, p141_1, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hc35, hlam, hphi, p141_1, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h0, h1, hc35, hlam, hphi, p141_1, u3ehi1]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [h140, hlam, p141_0]
                    · have p141_0 := h141c.1
                      have p141_1 := h141c.2.1
                      have p141_2 := h141c.2.2.1
                      have p141_3 := h141c.2.2.2
                      linarith only [hlam, p141_0]
                  · linarith only [h0, h140, h83, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h168 | h168
    · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
      · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
        · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
          · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
            · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
              · linarith only [h168, h173, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
              · linarith only [h169, h173, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
            · linarith only [h0, h170, h172, hlam]
          · linarith only [h0, h168, h169, h171, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
        · linarith only [h169, h170, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
        · linarith only [h169, h179, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
          · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
            · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
              · linarith only [h168, h169, h183, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                · linarith only [h168, h179, h185, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                  · rcases h3bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h0, hlam, p188_1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h179, h181, h182, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h169, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h179, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 3) (by simp) with h194 | h194
                      · linarith only [h0, h194, hlam]
                      · rcases p188_3 (m.d 1 3) (by simp) with h196 | h196
                        · rcases p188_3 (m.d 2 3) (by simp) with h197 | h197
                          · linarith only [h181, h197, hlam]
                          · rcases p188_3 (m.d 3 4) (by simp) with h199 | h199
                            · linarith only [h179, h182, h199, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h169, h199, hlam]
                        · linarith only [h0, h196, hlam]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      rcases p188_3 (m.d 0 3) (by simp) with h204 | h204
                      · linarith only [h0, h204, hlam]
                      · linarith only [h168, h204, hlam]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h168, h169, h181, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h168, h179, h181, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h168, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h181, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h183, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h185, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h168, hc34, hlam, hphi, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hc34, hlam, hphi, p188_1, u3ehi1]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hc34, hlam, hphi, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h168, h179, hc34, hlam, hphi, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h168, h182, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h182, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h181, h182, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p188_1, u3ehi2]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [h187, hlam, p188_0]
                    · have p188_0 := h188c.1
                      have p188_1 := h188c.2.1
                      have p188_2 := h188c.2.2.1
                      have p188_3 := h188c.2.2.2
                      linarith only [hlam, p188_0]
                  · linarith only [h168, h169, h187, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
              · linarith only [h168, h169, h225, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                · linarith only [h168, h182, h227, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                  · rcases h3bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h0, hlam, p230_1]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h0, h182, h229, hc34, hlam, hphi, p230_1, u3ehi2]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h169, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h179, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h182, h229, hc34, hlam, hphi, p230_1, u3ehi0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h182, h229, hc34, hlam, hphi, p230_1, u3ehi2]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h182, h229, hlam, p230_1]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h182, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h168, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h181, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h225, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h227, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h168, hc34, hlam, hphi, p230_1, u3ehi2]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hc34, hlam, hphi, p230_1, u3ehi1]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hc34, hlam, hphi, p230_1, u3ehi2]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hc34, hlam, hphi, p230_1, u3ehi4]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h168, hc35, hlam, hphi, p230_1, u3ehi2]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p230_1]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hc35, hlam, hphi, p230_1, u3ehi2]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [h229, hlam, p230_0]
                    · have p230_0 := h230c.1
                      have p230_1 := h230c.2.1
                      have p230_2 := h230c.2.2.1
                      have p230_3 := h230c.2.2.2
                      linarith only [hlam, p230_0]
                  · linarith only [h168, h169, h229, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h168, h181, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h258 | h258
      · rcases m.htr 0 3 5 (by decide) (by decide) with h259 | h259
        · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
          · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
            · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
              · rcases m.htr 2 3 5 (by decide) (by decide) with h263 | h263
                · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                  · rcases h3bigk with h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c | h265c
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h0, hlam, p265_1]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h168, hlam, p265_1]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h168, h260, h264, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h168, h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h258, h264, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h168, h258, h260, h264, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      rcases p265_3 (m.d 0 3) (by simp) with h274 | h274
                      · linarith only [h0, h274, hlam]
                      · linarith only [h258, h274, hlam]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      rcases p265_3 (m.d 0 3) (by simp) with h277 | h277
                      · linarith only [h0, h277, hlam]
                      · linarith only [h259, h277, hlam]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h258, h264, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h260, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h260, h264, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p265_1, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h258, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h258, hlam, hphi, ht0b, ht34, ht45, ht5b, p265_1, u0elo2, u3ehi1]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h262, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h258, hlam, hphi, ht0b, ht34, ht45, ht5b, p265_1, u0elo2, u3ehi4]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h259, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h261, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h263, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [h264, hlam, p265_0]
                    · have p265_0 := h265c.1
                      have p265_1 := h265c.2.1
                      have p265_2 := h265c.2.2.1
                      have p265_3 := h265c.2.2.2
                      linarith only [hlam, p265_0]
                  · rcases h3bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h0, hlam, p295_1]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h168, hlam, p295_1]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h168, h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h168, h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi4]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h258, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h168, h258, h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      rcases p295_3 (m.d 0 3) (by simp) with h304 | h304
                      · linarith only [h0, h304, hlam]
                      · linarith only [h258, h304, hlam]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      rcases p295_3 (m.d 0 3) (by simp) with h307 | h307
                      · linarith only [h0, h307, hlam]
                      · linarith only [h259, h307, hlam]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h259, h264, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p295_1, u3ehi3]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h260, hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h260, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h260, h264, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p295_1, u3ehi3]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h258, hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h259, h264, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1, u0elo2, u3ehi1]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h262, hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h264, hlam, p295_1]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h259, hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h261, hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h263, hlam, p295_0]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [h259, hc34, hlam, hphi, ht0b, ht45, ht5b, p295_1, u0elo2]
                    · have p295_0 := h295c.1
                      have p295_1 := h295c.2.1
                      have p295_2 := h295c.2.2.1
                      have p295_3 := h295c.2.2.2
                      linarith only [hlam, p295_0]
                · linarith only [h168, h259, h263, hlam]
              · linarith only [h168, h259, h262, hc34, hlam, hphi, u3ehi4]
            · linarith only [h168, h259, h260, h261, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
            · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                · rcases m.htr 3 4 5 (by decide) (by decide) with h331 | h331
                  · rcases h3bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h0, hlam, p332_1]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h168, hlam, p332_1]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h331, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u0elo2, u3ehi4]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u0elo2, u3ehi4]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h258, h260, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u3ehi4]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h260, hlam, p332_1]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      rcases p332_3 (m.d 0 3) (by simp) with h341 | h341
                      · linarith only [h0, h341, hlam]
                      · linarith only [h258, h341, hlam]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      rcases p332_3 (m.d 0 3) (by simp) with h344 | h344
                      · linarith only [h0, h344, hlam]
                      · linarith only [h259, h344, hlam]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h258, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u3ehi4]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p332_1]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      rcases p332_3 (m.d 0 3) (by simp) with h350 | h350
                      · linarith only [h168, h350, hlam]
                      · linarith only [h258, h350, hlam]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      rcases p332_3 (m.d 0 3) (by simp) with h353 | h353
                      · linarith only [h168, h353, hlam]
                      · linarith only [h259, h353, hlam]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h258, hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h0, h258, hlam, p332_1]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h329, hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h258, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u0elo2, u3ehi4]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h259, hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h328, hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h330, hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [h331, hlam, p332_0]
                    · have p332_0 := h332c.1
                      have p332_1 := h332c.2.1
                      have p332_2 := h332c.2.2.1
                      have p332_3 := h332c.2.2.2
                      linarith only [hlam, p332_0]
                  · rcases h3bigk with h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h0, hlam, p366_1]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h168, hlam, p366_1]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p366_1, u0elo2, u3ehi3]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p366_1, u0elo2, u3ehi4]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h258, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p366_1, u3ehi3]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h260, hlam, p366_1]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      rcases p366_3 (m.d 0 3) (by simp) with h375 | h375
                      · linarith only [h0, h375, hlam]
                      · linarith only [h258, h375, hlam]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      rcases p366_3 (m.d 0 3) (by simp) with h378 | h378
                      · linarith only [h0, h378, hlam]
                      · linarith only [h259, h378, hlam]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h259, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p366_1, u3ehi3]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p366_1]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      rcases p366_3 (m.d 0 3) (by simp) with h384 | h384
                      · linarith only [h168, h384, hlam]
                      · linarith only [h258, h384, hlam]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      rcases p366_3 (m.d 0 3) (by simp) with h387 | h387
                      · linarith only [h168, h387, hlam]
                      · linarith only [h259, h387, hlam]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h258, hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h0, h259, h331, hlam, p366_1]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h329, hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h331, hlam, p366_1]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h259, hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h328, hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h330, hlam, p366_0]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [h259, hlam, hphi, ht0b, ht34, ht45, ht5b, p366_1, u0elo2, u3ehi3]
                    · have p366_0 := h366c.1
                      have p366_1 := h366c.2.1
                      have p366_2 := h366c.2.2.1
                      have p366_3 := h366c.2.2.2
                      linarith only [hlam, p366_0]
                · linarith only [h168, h259, h330, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h259, h260, h329, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h259, h328, hlam]
        · linarith only [h258, h259, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h404 | h404
        · linarith only [h258, h404, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
          · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
            · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
              · linarith only [h258, h406, h408, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
                · linarith only [h408, h410, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                  · rcases h3bigk with h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h0, hlam, p413_1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h168, hlam, p413_1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h258, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h404, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      rcases p413_3 (m.d 0 3) (by simp) with h419 | h419
                      · linarith only [h0, h419, hlam]
                      · rcases p413_3 (m.d 1 3) (by simp) with h421 | h421
                        · rcases p413_3 (m.d 2 3) (by simp) with h422 | h422
                          · linarith only [h406, h422, hlam]
                          · linarith only [h168, h422, hlam]
                        · linarith only [h0, h421, hlam]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      rcases p413_3 (m.d 0 3) (by simp) with h427 | h427
                      · linarith only [h0, h427, hlam]
                      · rcases p413_3 (m.d 1 3) (by simp) with h429 | h429
                        · rcases p413_3 (m.d 2 3) (by simp) with h430 | h430
                          · linarith only [h406, h430, hlam]
                          · rcases p413_3 (m.d 3 4) (by simp) with h432 | h432
                            · linarith only [h168, h432, hc02, hc34, hlam, hphi, ht23, p413_1]
                            · linarith only [h408, h432, hlam]
                        · linarith only [h406, h429, hlam]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h258, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p413_1, u3ehi0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h168, h406, h410, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p413_1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h407, h410, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p413_1, u3ehi0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h406, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h408, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h410, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hc34, hlam, hphi, p413_1, u3ehi0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hc34, hlam, hphi, p413_1, u3ehi1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h168, hc02, hc34, hlam, hphi, ht23, p413_1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h168, h410, hc02, hc34, hlam, hphi, ht23, p413_1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h407, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p413_1, u3ehi0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h407, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h168, h406, h407, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p413_1]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [h412, hlam, p413_0]
                    · have p413_0 := h413c.1
                      have p413_1 := h413c.2.1
                      have p413_2 := h413c.2.2.1
                      have p413_3 := h413c.2.2.2
                      linarith only [hlam, p413_0]
                  · linarith only [h258, h412, hc45, hlam, hphi, ht34, u3ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
              · linarith only [h258, h406, h454, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                · linarith only [h406, h407, h456, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                  · rcases h3bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h168, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h258, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h404, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h407, h458, hc34, hlam, hphi, p459_1, u3ehi0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h407, h458, hc34, hlam, hphi, p459_1, u3ehi2]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h407, h458, hlam, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h407, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h406, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p459_1, u3ehi0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h406, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h454, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h456, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hc34, hlam, hphi, p459_1, u3ehi0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hc34, hlam, hphi, p459_1, u3ehi1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h168, hc02, hc34, hlam, hphi, ht23, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hc34, hlam, hphi, p459_1, u3ehi4]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hc35, hlam, hphi, p459_1, u3ehi0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h168, hc02, hc35, hlam, hphi, ht23, p459_1]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [h458, hlam, p459_0]
                    · have p459_0 := h459c.1
                      have p459_1 := h459c.2.1
                      have p459_2 := h459c.2.2.1
                      have p459_3 := h459c.2.2.2
                      linarith only [hlam, p459_0]
                  · linarith only [h258, h458, hc45, hlam, hphi, ht34, u3ehi0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h486 | h486
            · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
              · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                  · rcases h3bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h0, hlam, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h168, hlam, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h258, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h404, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      rcases p490_3 (m.d 0 3) (by simp) with h496 | h496
                      · linarith only [h0, h496, hlam]
                      · rcases p490_3 (m.d 1 3) (by simp) with h498 | h498
                        · rcases p490_3 (m.d 2 3) (by simp) with h499 | h499
                          · rcases p490_3 (m.d 3 4) (by simp) with h500 | h500
                            · linarith only [h404, h486, h500, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h258, h500, hlam]
                          · linarith only [h168, h499, hlam]
                        · linarith only [h0, h498, hlam]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h406, hlam, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h258, h406, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h404, h406, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      rcases p490_3 (m.d 0 3) (by simp) with h509 | h509
                      · linarith only [h168, h509, hlam]
                      · rcases p490_3 (m.d 1 3) (by simp) with h511 | h511
                        · linarith only [h406, h511, hlam]
                        · linarith only [h0, h511, hlam]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h404, h489, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h404, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hc34, hlam, hphi, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h404, h486, h487, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h487, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h404, h487, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h486, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p490_1, u3ehi0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h486, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h488, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h489, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                  · linarith only [h258, h489, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h406, h486, h488, hlam]
              · linarith only [h406, h486, h487, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
              · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                · linarith only [h0, h486, h532, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h258, h531, h532, hc35, hlam, hphi, u3ehi0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
                · linarith only [h531, h535, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h537 | h537
                  · rcases h3bigk with h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h0, hlam, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h168, hlam, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h258, hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h404, hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h406, h535, h537, hc34, hlam, hphi, p538_1, u3ehi0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h406, hlam, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h406, h535, h537, hlam, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h486, hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h535, h537, hc34, hlam, hphi, p538_1, u3ehi0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h535, h537, hc34, hlam, hphi, p538_1, u3ehi1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h531, hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h535, hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hc34, hlam, hphi, p538_1, u3ehi0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h406, hc12, hc34, hlam, hphi, ht23, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hc34, hlam, hphi, p538_1, u3ehi4]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hc35, hlam, hphi, p538_1, u3ehi0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h0, h406, hc01, hc35, hlam, hphi, ht12, ht23, p538_1]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [h537, hlam, p538_0]
                    · have p538_0 := h538c.1
                      have p538_1 := h538c.2.1
                      have p538_2 := h538c.2.2.1
                      have p538_3 := h538c.2.2.2
                      linarith only [hlam, p538_0]
                  · linarith only [h258, h537, hc45, hlam, hphi, ht34, u3ehi0]

end R2N4
