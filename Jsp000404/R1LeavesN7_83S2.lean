import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_0_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
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
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h1, h2, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, h2, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · linarith only [h0, h13, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h10, h15, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h12, h17, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h10, h12, h19, hlam]
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
                        linarith only [h12, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1, u0elo2, u3ehi2]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h10, h21, hc34, hlam, hphi, p22_1, u3ehi2]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h2, hlam, p22_0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h10, hlam, p22_0]
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
                        linarith only [h13, hlam, p22_0]
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
                        linarith only [h12, hlam, p22_0]
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
                        linarith only [hc34, hlam, hphi, p22_1, u3ehi0]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h12, hc34, hlam, hphi, p22_1, u3ehi2]
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
                        linarith only [hc34, hlam, hphi, p22_1, u3ehi4]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h0, h12, hc35, hlam, hphi, p22_1, u3ehi2]
                      · have p22_0 := h22c.1
                        have p22_1 := h22c.2.1
                        have p22_2 := h22c.2.2.1
                        have p22_3 := h22c.2.2.2
                        linarith only [h12, hc35, hlam, hphi, p22_1, u3ehi2]
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
                    · linarith only [h0, h12, h2, h21, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h1, h12, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
      · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
        · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
          · linarith only [h1, h50, h52, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
            · linarith only [h0, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h50, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · linarith only [h50, h51, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
        · linarith only [h50, h58, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
          · linarith only [h1, h60, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h50, h62, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h58, h64, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h50, h66, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h58, h68, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                    · rcases h3bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p71_1, u0elo2, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h1, hlam, p71_1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h50, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h58, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h0, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h60, hlam, p71_1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h62, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h64, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h68, h70, hc34, hlam, hphi, p71_1, u3ehi0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h68, h70, hc34, hlam, hphi, p71_1, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h66, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h68, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, p71_1, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hc34, hlam, hphi, p71_1, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h1, hc02, hc34, hlam, hphi, ht23, p71_1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hc34, hlam, hphi, p71_1, u3ehi4]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h0, hc35, hlam, hphi, p71_1, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hc35, hlam, hphi, p71_1, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h0, h1, hc35, hlam, hphi, p71_1, u3ehi1]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [h70, hlam, p71_0]
                      · have p71_0 := h71c.1
                        have p71_1 := h71c.2.1
                        have p71_2 := h71c.2.2.1
                        have p71_3 := h71c.2.2.2
                        linarith only [hlam, p71_0]
                    · linarith only [h0, h50, h70, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h98 | h98
    · rcases m.htr 0 3 4 (by decide) (by decide) with h99 | h99
      · rcases m.htr 0 3 5 (by decide) (by decide) with h100 | h100
        · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
          · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
            · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h98, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                · linarith only [h0, h101, h104, h99, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
              · linarith only [h0, h100, h103, hlam]
            · linarith only [h0, h102, h99, hlam]
          · linarith only [h101, h98, hc12, hlam, hphi, u2elo0]
        · linarith only [h100, h99, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
        · linarith only [h111, h99, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
          · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
            · linarith only [h113, h114, h98, h99, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
              · linarith only [h111, h114, h116, h98, hc34, hlam, hphi, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                · linarith only [h0, h114, h118, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h116, h120, h98, hc01, hlam, hphi, ht12, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                    · rcases h3bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h0, hlam, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p123_1, u0elo2, u3ehi2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h99, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h111, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h116, h122, hc34, hlam, hphi, p123_1, u3ehi0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h116, h122, hc34, hlam, hphi, p123_1, u3ehi2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h114, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h116, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h98, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h113, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h118, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h120, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h98, hc34, hlam, hphi, p123_1, u3ehi2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hc34, hlam, hphi, p123_1, u3ehi2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hc34, hlam, hphi, p123_1, u3ehi4]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h98, hc35, hlam, hphi, p123_1, u3ehi2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hc35, hlam, hphi, p123_1, u3ehi2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h122, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                    · linarith only [h122, h98, h99, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h113, h98, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
      · rcases m.htr 0 3 5 (by decide) (by decide) with h152 | h152
        · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
          · linarith only [h153, h98, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
            · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
              · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
                    · rcases h3bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h0, hlam, p160_1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h98, hlam, p160_1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h159, hlam, hphi, ht0b, ht34, ht45, ht5b, p160_1, u0elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h0, h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h153, hlam, p160_1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h153, h159, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h151, h159, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi1]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h159, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p160_1, u2elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h151, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h155, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h157, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h151, hlam, hphi, ht0b, ht34, ht45, ht5b, p160_1, u0elo2, u3ehi4]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h152, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h156, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h158, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [h159, hlam, p160_0]
                      · have p160_0 := h160c.1
                        have p160_1 := h160c.2.1
                        have p160_2 := h160c.2.2.1
                        have p160_3 := h160c.2.2.2
                        linarith only [hlam, p160_0]
                    · rcases h3bigk with h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h0, hlam, p186_1]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h98, hlam, p186_1]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h0, h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi3]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h0, h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi4]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h153, hlam, p186_1]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi3]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h153, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi4]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h151, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi3]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi1]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi3]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p186_1, u2elo2, u3ehi4]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h151, hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h155, hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h157, hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h159, hlam, p186_1]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h152, hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h156, hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [h158, hlam, p186_0]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hc35, hlam, hphi, p186_1, u3ehi3]
                      · have p186_0 := h186c.1
                        have p186_1 := h186c.2.1
                        have p186_2 := h186c.2.2.1
                        have p186_3 := h186c.2.2.2
                        linarith only [hlam, p186_0]
                  · linarith only [h152, h153, h158, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h151, h153, h157, hlam]
              · linarith only [h0, h152, h156, hlam]
            · linarith only [h0, h151, h155, hlam]
        · linarith only [h151, h152, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h217 | h217
        · linarith only [h151, h217, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
          · linarith only [h219, h98, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
            · linarith only [h151, h219, h221, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
              · linarith only [h217, h221, h223, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                · linarith only [h221, h225, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                  · linarith only [h0, h223, h225, h227, hc01, hc34, hlam, hphi, ht12, ht23]
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
                        linarith only [h98, hlam, p230_1]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h151, hlam, p230_0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h217, hlam, p230_0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h219, h227, h229, hc34, hlam, hphi, p230_1, u3ehi0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [hlam, p230_0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h219, hlam, p230_1]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h221, hlam, p230_0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h223, hlam, p230_0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h227, h229, hc34, hlam, hphi, p230_1, u3ehi0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h227, h229, hc34, hlam, hphi, p230_1, u3ehi1]
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
                        linarith only [hc34, hlam, hphi, p230_1, u3ehi0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p230_1]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h219, hc12, hc34, hlam, hphi, ht23, p230_1]
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
                        linarith only [hc35, hlam, hphi, p230_1, u3ehi0]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p230_1]
                      · have p230_0 := h230c.1
                        have p230_1 := h230c.2.1
                        have p230_2 := h230c.2.2.1
                        have p230_3 := h230c.2.2.2
                        linarith only [h0, h219, hc01, hc35, hlam, hphi, ht12, ht23, p230_1]
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
                    · linarith only [h151, h229, hc45, hlam, hphi, ht34, u3ehi0]

theorem r1l7_10_12_23_L_0_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h4, h5, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h3, h5, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h11, h12, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h11, h14, h5, hc23, hlam, hphi, u3elo3]
              · linarith only [h11, h3, hc13, hlam, hphi, u3elo0]
          · linarith only [h2, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h1, h21, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h19, h23, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h20, h23, h3, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
              · linarith only [h20, h26, h3, hc03, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                · linarith only [h0, h19, h28, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h19, h3, h30, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                    · rcases h3bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h19, h3, h32, hc23, hlam, hphi, p33_1, u3elo3]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h3, h32, hc23, hlam, hphi, p33_1, u3elo3]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h3, h32, hlam, p33_1]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h3, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h1, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hc23, hlam, hphi, p33_1, u3elo1]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h20, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h26, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h2, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h19, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h28, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h30, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hc03, hlam, hphi, p33_1, u3elo3]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h19, hc23, hlam, hphi, p33_1, u3elo3]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hc23, hlam, hphi, p33_1, u3elo3]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h1, h19, h3, hc23, hlam, hphi, p33_1, u3elo3]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h1, h19, hc23, hlam, hphi, p33_1, u3elo4]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h19, hc23, hlam, hphi, p33_1, u3elo4]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hc23, hlam, hphi, p33_1, u3elo4]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [h32, hlam, p33_0]
                      · have p33_0 := h33c.1
                        have p33_1 := h33c.2.1
                        have p33_2 := h33c.2.2.1
                        have p33_3 := h33c.2.2.2
                        linarith only [hlam, p33_0]
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
                        linarith only [h19, hc23, hlam, hphi, p59_1, u3elo0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hc23, hlam, hphi, p59_1, u3elo0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h28, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p59_1, u3elo4]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h3, hlam, p59_0]
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
                        linarith only [hc23, hlam, hphi, p59_1, u3elo1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h20, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h26, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h2, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h19, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h28, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h30, hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h32, hc03, hc45, hlam, hphi, ht34, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h19, h32, hc23, hc45, hlam, hphi, ht34, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h32, hc23, hc45, hlam, hphi, ht34, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h32, hlam, p59_1]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h1, h19, hc23, hlam, hphi, p59_1, u3elo4]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h19, hc23, hlam, hphi, p59_1, u3elo4]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hc23, hlam, hphi, p59_1, u3elo4]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [h19, h20, hc23, hlam, hphi, p59_1, u3elo4]
                      · have p59_0 := h59c.1
                        have p59_1 := h59c.2.1
                        have p59_2 := h59c.2.2.1
                        have p59_3 := h59c.2.2.2
                        linarith only [hlam, p59_0]
          · linarith only [h19, h2, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h86 | h86
        · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
          · linarith only [h0, h2, h87, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h1, h89, h93, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases h3bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h90, h93, hc34, hlam, hphi, ht0b, ht45, ht5b, p95_1, u0elo2]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h2, hlam, p95_1]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 3) (by simp) with h99 | h99
                        · rcases p95_3 (m.d 1 3) (by simp) with h100 | h100
                          · linarith only [h1, h100, hlam]
                          · linarith only [h100, h89, hlam]
                        · linarith only [h99, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 3) (by simp) with h104 | h104
                        · rcases p95_3 (m.d 1 3) (by simp) with h105 | h105
                          · linarith only [h1, h105, hlam]
                          · linarith only [h105, h90, hlam]
                        · linarith only [h104, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h1, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h87, hlam, p95_1]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p95_1, u0elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h1, h93, hc34, hlam, hphi, ht0b, ht45, ht5b, p95_1, u0elo0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hc03, hlam, hphi, p95_1, u3elo2]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hc13, hlam, hphi, p95_1, u3elo2]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 3) (by simp) with h117 | h117
                        · linarith only [h117, h2, hlam]
                        · linarith only [h1, h117, h90, h93, hlam]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        rcases p95_3 (m.d 0 3) (by simp) with h120 | h120
                        · linarith only [h120, h2, hlam]
                        · linarith only [h120, h86, hlam]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h1, h90, h93, hlam, p95_1]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h89, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h91, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h93, hlam, p95_1]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h86, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h90, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h92, hlam, p95_0]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [h1, h90, hc34, hlam, hphi, ht0b, ht45, ht5b, p95_1, u0elo2]
                      · have p95_0 := h95c.1
                        have p95_1 := h95c.2.1
                        have p95_2 := h95c.2.2.1
                        have p95_3 := h95c.2.2.2
                        linarith only [hlam, p95_0]
                  · linarith only [h1, h2, h90, h92, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h1, h2, h89, h91, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h86, h89, h90, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
              · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                · linarith only [h136, h137, h89, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h0, h137, h2, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h136, h2, h86, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
          · linarith only [h0, h141, h2, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
            · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
              · linarith only [h1, h144, h86, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h1, h143, h147, h86, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h147, h2, hc02, hlam, hphi, ht23, u3elo4]
                · linarith only [h0, h1, h143, h146, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
              · linarith only [h1, h151, h86, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                · linarith only [h143, h153, hc13, hlam, hphi, u3elo2]
                · linarith only [h0, h153, h2, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h157 | h157
    · rcases m.htr 0 2 3 (by decide) (by decide) with h158 | h158
      · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
        · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
          · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
            · linarith only [h0, h157, h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
              · linarith only [h0, h157, h163, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h159, h160, h163, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h160, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
          · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
            · linarith only [h0, h157, h168, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
              · linarith only [h0, h157, h159, h170, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                · linarith only [h167, h168, h172, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h157, h159, h167, h174, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
                    · rcases h3bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h159, h176, hc13, hlam, hphi, p177_1, u3elo3]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h159, h176, hc23, hlam, hphi, p177_1, u3elo3]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h159, h176, hlam, p177_1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h159, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h157, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h0, h157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo1]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h168, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h170, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h158, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h167, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h172, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h174, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hc03, hlam, hphi, p177_1, u3elo3]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h167, hc23, hlam, hphi, p177_1, u3elo3]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hc23, hlam, hphi, p177_1, u3elo3]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h157, h159, h167, hc23, hlam, hphi, p177_1, u3elo3]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h157, h167, hc23, hlam, hphi, p177_1, u3elo4]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h167, hc23, hlam, hphi, p177_1, u3elo4]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hc23, hlam, hphi, p177_1, u3elo4]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [h176, hlam, p177_0]
                      · have p177_0 := h177c.1
                        have p177_1 := h177c.2.1
                        have p177_2 := h177c.2.2.1
                        have p177_3 := h177c.2.2.2
                        linarith only [hlam, p177_0]
                    · rcases h3bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h167, hc23, hlam, hphi, p203_1, u3elo0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h0, h157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p203_1, u2elo1]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h159, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo4]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h159, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h157, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hc23, hlam, hphi, p203_1, u3elo1]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h168, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h170, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h158, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h167, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h172, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h174, hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hc03, hlam, hphi, p203_1, u3elo3]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h167, hc23, hlam, hphi, p203_1, u3elo3]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hc23, hlam, hphi, p203_1, u3elo3]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hlam, p203_0]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h176, hlam, p203_1]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h157, h167, hc23, hlam, hphi, p203_1, u3elo4]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h167, hc23, hlam, hphi, p203_1, u3elo4]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hc23, hlam, hphi, p203_1, u3elo4]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [h167, h168, hc23, hlam, hphi, p203_1, u3elo4]
                      · have p203_0 := h203c.1
                        have p203_1 := h203c.2.1
                        have p203_2 := h203c.2.2.1
                        have p203_3 := h203c.2.2.2
                        linarith only [hlam, p203_0]
          · linarith only [h0, h167, hc01, hlam, hphi, ht12, u2elo2]
      · linarith only [h0, h157, h158, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h231 | h231
      · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
        · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
          · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
            · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
              · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h231, h236, h238, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases h3bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h157, hlam, p240_1]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hc23, hlam, hphi, p240_1, u3elo0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        rcases p240_3 (m.d 0 3) (by simp) with h244 | h244
                        · rcases p240_3 (m.d 1 3) (by simp) with h245 | h245
                          · rcases p240_3 (m.d 2 3) (by simp) with h246 | h246
                            · linarith only [h231, h246, hlam]
                            · linarith only [h236, h246, hlam]
                          · linarith only [h234, h245, hlam]
                        · linarith only [h244, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        rcases p240_3 (m.d 0 3) (by simp) with h251 | h251
                        · rcases p240_3 (m.d 1 3) (by simp) with h252 | h252
                          · rcases p240_3 (m.d 2 3) (by simp) with h253 | h253
                            · linarith only [h231, h253, hlam]
                            · linarith only [h237, h253, hlam]
                          · linarith only [h235, h252, hlam]
                        · linarith only [h251, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hc03, hlam, hphi, p240_1, u3elo1]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h237, h238, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p240_1, u3elo1]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        rcases p240_3 (m.d 0 3) (by simp) with h261 | h261
                        · linarith only [h157, h261, hlam]
                        · linarith only [h231, h237, h238, h261, hlam]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        rcases p240_3 (m.d 0 3) (by simp) with h264 | h264
                        · linarith only [h157, h264, hlam]
                        · linarith only [h232, h264, hlam]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h231, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h233, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h0, h231, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1, u2elo1]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h0, h231, h238, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p240_1, u2elo1]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hc03, hlam, hphi, p240_1, u3elo3]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h234, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h236, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h238, hlam, p240_1]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h232, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h235, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h237, hlam, p240_0]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1, u0elo2]
                      · have p240_0 := h240c.1
                        have p240_1 := h240c.2.1
                        have p240_2 := h240c.2.2.1
                        have p240_3 := h240c.2.2.2
                        linarith only [hlam, p240_0]
                  · linarith only [h157, h232, h236, h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                · linarith only [h234, h236, hc23, hlam, hphi, u3elo1]
              · linarith only [h157, h232, h235, hlam]
            · linarith only [h157, h234, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h233, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
              · linarith only [h232, h289, hc03, hlam, hphi, u3elo1]
              · linarith only [h157, h289, hc01, hlam, hphi, ht12, ht23, u3elo4]
            · linarith only [h157, h288, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h231, h287, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h294 | h294
        · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
          · linarith only [h0, h231, h295, hc01, hlam, hphi, ht12, u2elo1]
          · linarith only [h0, h295, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
          · linarith only [h0, h231, h298, hc01, hlam, hphi, ht12, u2elo1]
          · linarith only [h0, h298, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
