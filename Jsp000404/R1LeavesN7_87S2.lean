import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_14_25_L_0_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
        · linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
        · linarith only [h0, h1, h5, hc13, hlam, hphi, ht34, u4elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
      · linarith only [h10, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
        · linarith only [h12, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h0, h10, h12, h14, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h0, h10, h14, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]

theorem r1l7_11_14_25_L_0_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
            · linarith only [h4, h5, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h1, h10, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
              · linarith only [h10, h3, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h14, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
            · linarith only [h13, h14, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
            · linarith only [h1, h13, h17, h3, hlam, hphi, u5ehi7, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h1, h19, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h22, h3, hc04, hlam, hphi, u4elo2]
                  · linarith only [h13, h22, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h1, h13, h21, h25, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h13, h25, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
      · linarith only [h30, h31, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
      · linarith only [h30, h34, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
        · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
          · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
            · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h37, h41, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                  · linarith only [h30, h36, h40, h41, hc34, hlam, hphi, u4elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h37, h44, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                  · linarith only [h30, h36, h44, hc24, hlam, hphi, u4elo1]
              · linarith only [h30, h36, h39, hlam]
            · linarith only [h0, h30, h36, h38, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1, u5ehi9, u5elo2]
          · linarith only [h0, h37, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
          · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
              · linarith only [h36, h52, hc04, hlam, hphi, u4elo1]
              · linarith only [h30, h52, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h50, h51, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h0, h50, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem r1l7_11_14_25_L_R_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · rcases h5bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h4, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h6, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht12, ht23, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hlam, hphi, ht12, ht23, ht34, p10_1, u1ehi4, u4elo3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h8, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                    · linarith only [h4, h9, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h7, h8, hc24, hlam, hphi, u4elo0]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h3, h4, h6, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo0]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
              · linarith only [h0, h3, h44, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                · linarith only [h43, h44, h46, hlam]
                · linarith only [h46, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h43, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
          · linarith only [h1, h42, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h53 | h53
    · linarith only [h0, h53, hc12, hlam, hphi, u1ehi3]
    · linarith only [h53, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_11_14_25_L_R_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
  · linarith only [h0, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]

theorem r1l7_11_14_25_L_R_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · linarith only [h1, h3, h4, hc24, hlam, hphi, u4elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc12, hlam, hphi, u1ehi3]
    · linarith only [h10, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_11_14_25_L_R_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h7, h9, hc24, hlam, hphi, u4elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h12, h7, hc24, hlam, hphi, u4elo1]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
            · linarith only [h4, h5, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h18, h19, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h18, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
          · linarith only [h0, h2, h24, h25, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
              · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h2, h27, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h29, h31, hc24, hlam, hphi, u4elo1]
                  · linarith only [h0, h2, h30, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h29, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h28, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
            · linarith only [h27, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
        · linarith only [h0, h24, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
    · linarith only [h0, h40, hc12, hlam, hphi, u1ehi4]
    · linarith only [h40, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_14_25_L_R_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h3, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · rcases h5emax with h9 | h9 | h9 | h9 | h9
        · linarith only [h0, h9, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h9, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
      · rcases h5emax with h16 | h16 | h16 | h16 | h16
        · linarith only [h0, h16, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h16, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h16, hlam, ht45, u4ehi2]
        · linarith only [h1, h15, h16, hlam, ht45, u4ehi2]
        · linarith only [h1, h16, hlam, ht45, u4ehi2]
      · rcases h5emax with h22 | h22 | h22 | h22 | h22
        · linarith only [h0, h22, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h22, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h22, hlam, ht45, u4ehi2]
        · linarith only [h15, h22, hlam, ht45, u4ehi3]
        · linarith only [h1, h22, hlam, ht45, u4ehi2]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
      · rcases h5emax with h30 | h30 | h30 | h30 | h30
        · linarith only [h0, h30, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h30, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h30, hlam, ht45, u4ehi4]
        · linarith only [h29, h30, hlam, ht45, u4ehi4]
        · linarith only [h30, hlam, ht45, u4ehi4]
      · rcases h5emax with h36 | h36 | h36 | h36 | h36
        · linarith only [h0, h36, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h36, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h29, h36, hlam, ht45, u4ehi3]
        · linarith only [h29, h36, hlam, ht45, u4ehi3]
        · linarith only [h29, h36, hlam, ht45, u4ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
      · rcases h5emax with h43 | h43 | h43 | h43 | h43
        · linarith only [h0, h43, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h43, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h43, hlam, ht45, u4ehi2]
        · linarith only [h42, h43, hlam, ht45, u4ehi4]
        · linarith only [h43, hlam, ht45, u4ehi4]
      · rcases h5emax with h49 | h49 | h49 | h49 | h49
        · linarith only [h0, h49, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h49, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h49, hlam, ht45, u4ehi2]
        · linarith only [h42, h49, hlam, ht45, u4ehi3]
        · linarith only [h28, h49, hlam, ht45, u4ehi2]

theorem r1l7_11_14_25_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h4, h5, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h11, hlam, hphi, ht45, u4ehi2, u5elo4]
              · linarith only [h5, h6, hlam, hphi, ht45, u4ehi1, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · linarith only [h15, h16, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h15, h18, h5, hc23, hc34, hlam, hphi]
              · linarith only [h15, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                      · linarith only [h1, h22, h27, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h27, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h26, hlam, hphi, ht45, u4ehi2, u5elo4]
                  · linarith only [h23, h25, h3, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                · linarith only [h24, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h22, h23, hlam, hphi, ht45, u4ehi3, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
              · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                · linarith only [h22, h34, h35, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h35, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h34, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
    · linarith only [h0, h42, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
      · linarith only [h0, h44, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h46 | h46
        · linarith only [h0, h46, hc12, hlam, hphi, u1ehi4]
        · linarith only [h46, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_23_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · linarith only [h4, hc23, hlam, hphi, u3elo4]
        · linarith only [h3, hc13, hlam, hphi, u3elo3]
      · linarith only [h2, hc12, hlam, hphi, ht23, u3elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h10, h12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · linarith only [h12, hc13, hlam, hphi, u3elo3]
      · linarith only [h0, h11, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · linarith only [h10, hc01, hlam, hphi, ht12, ht23, u3elo1]

theorem r1l7_11_23_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
  · linarith only [h0, hc34, hlam, hphi, u3ehi1]

theorem r1l7_11_23_L_R_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  linarith only [hlam, hphi, ht12, ht23, u1ehi2, u3elo1]

theorem r1l7_11_23_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
        · linarith only [h4, hc34, hlam, hphi, u3ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
          · linarith only [h10, h12, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h12, hc34, hlam, hphi, u3ehi2]
        · linarith only [h11, h8, hc34, hlam, hphi, ht12, ht23, u1ehi0]
      · linarith only [h0, h10, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_23_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases h3bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc13, hlam, hphi, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc23, hlam, hphi, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h14 | h14
                      · rcases p10_3 (m.d 1 3) (by simp) with h15 | h15
                        · linarith only [h1, h15, hlam]
                        · linarith only [h15, h4, hlam]
                      · linarith only [h14, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h19 | h19
                      · rcases p10_3 (m.d 1 3) (by simp) with h20 | h20
                        · linarith only [h1, h20, hlam]
                        · linarith only [h20, h5, hlam]
                      · linarith only [h19, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10_1, u3elo1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h27 | h27
                      · rcases p10_3 (m.d 1 3) (by simp) with h28 | h28
                        · rcases p10_3 (m.d 2 3) (by simp) with h29 | h29
                          · linarith only [h29, h3, hlam]
                          · linarith only [h29, h6, hlam]
                        · linarith only [h28, hlam, p10_0]
                      · linarith only [h1, h27, h7, h8, hlam, hphi, ht12, ht23, u1ehi2, u3elo2]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h34 | h34
                      · rcases p10_3 (m.d 1 3) (by simp) with h35 | h35
                        · rcases p10_3 (m.d 2 3) (by simp) with h36 | h36
                          · linarith only [h3, h36, hlam]
                          · linarith only [h36, h7, hlam]
                        · linarith only [h35, hlam, p10_0]
                      · linarith only [h1, h34, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h5, hlam, hphi, ht12, ht23, p10_1, u1ehi4, u3elo3]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h4, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h6, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h8, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h1, h3, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                · linarith only [h1, h5, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h1, h4, h6, hc23, hlam, hphi, u3elo0]
            · linarith only [h5, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
    · linarith only [h0, h63, hc12, hlam, hphi, u1ehi2]
    · linarith only [h63, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_25_L_R_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5elo := hb5.1
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem r1l7_12_13_25_L_0_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
      · linarith only [h0, h1, h3, hc23, hlam, hphi, u3elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
      · linarith only [h0, h8, hc02, hlam, hphi, ht23, u3elo4]

theorem r1l7_12_13_25_L_0_L_R_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · linarith only [h0, h1, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h6, h8, hc34, hlam, hphi, u3ehi2]
        · linarith only [h0, h8, hc45, hlam, hphi, ht34, u3ehi2]

theorem r1l7_12_13_25_L_0_L_R_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hc34, hlam, hphi, u3ehi4]
    · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]

theorem r1l7_12_13_25_L_R_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
    · linarith only [h1, hlam, hphi, ht23, u2ehi2, u3elo4]
  · linarith only [h0, hlam, hphi, ht23, u2ehi2, u3elo3]

theorem r1l7_12_13_25_L_R_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc15, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc35, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht34, ht45, p3_1, u3ehi4, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u5elo2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, hphi, ht34, ht45, p3_1, u3ehi4, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc45, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc15, hlam, hphi, p3_1, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u5elo4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h0, h1, h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo1]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
  · linarith only [h0, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_12_13_25_L_R_L_R_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
            · linarith only [h5, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h3, h9, hc34, hlam, hphi, u3ehi4]
          · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h16, hc23, hlam, hphi, u2ehi4]
      · linarith only [h16, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_12_14_25_L_0_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
      · linarith only [h0, h1, h3, hc34, hlam, hphi, u4elo4]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
      · linarith only [h0, h8, hc23, hlam, hphi, ht34, u4elo4]

theorem r1l7_12_14_25_L_0_L_R_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
      · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
        · linarith only [h0, h1, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h1, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
            · linarith only [h11, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · linarith only [h0, h1, h11, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
          · linarith only [h19, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h18, h19, h21, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h14, h18, h19, h21, h23, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h18, h19, h23, hc45, hlam, hphi, u4ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
          · linarith only [h26, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
            · linarith only [h28, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h18, h28, h30, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h18, h30, hc12, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_12_14_25_L_0_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h2, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
            · linarith only [h5, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h1, h4, hlam, hphi, ht45, u4ehi1, u5elo0]
        · linarith only [h0, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
            · linarith only [h10, h12, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
            · linarith only [h11, h12, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
          · linarith only [h11, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h0, h10, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht45, u4ehi0, u5elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
    · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
      · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
        · linarith only [h0, h20, hc02, hlam, hphi, u2elo1]
        · linarith only [h19, h20, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
        · linarith only [h0, h19, h23, hc02, hlam, hphi, u2elo3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
              · rcases h5bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc15, hlam, hphi, p28_1, u5elo0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h0, hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, p28_1, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h0, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc05, hlam, hphi, p28_1, u5elo1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h23, hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h23, h27, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h23, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h18, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc15, hlam, hphi, p28_1, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h27, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h18, hlam, hphi, ht45, p28_1, u4ehi4, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h25, hlam, hphi, ht45, p28_1, u4ehi4, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc25, hlam, hphi, p28_1, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, hphi, ht45, p28_1, u4ehi4, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h18, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h25, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h26, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h27, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
              · linarith only [h18, h27, hlam, hphi, ht45, u4ehi3, u5elo0]
            · linarith only [h19, h25, h26, hlam]
          · linarith only [h25, hlam, hphi, ht45, u4ehi1, u5elo4]
    · linarith only [h18, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem r1l7_12_14_25_L_R_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
  · linarith only [h0, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]

theorem r1l7_12_14_25_L_R_L_0_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
          · linarith only [h1, h3, h4, hc34, hlam, hphi, u4elo0]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi3]
    · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem r1l7_12_14_25_L_R_L_0_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
          · linarith only [h3, h4, hc34, hlam, hphi, u4elo2]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi4]
    · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_12_14_25_L_R_L_R_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h3, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · rcases h5emax with h9 | h9 | h9 | h9 | h9
        · linarith only [h0, h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h1, h9, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h9, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
      · rcases h5emax with h16 | h16 | h16 | h16 | h16
        · linarith only [h0, h16, hlam, ht45, u4ehi4]
        · linarith only [h1, h16, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h1, h16, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h15, h16, hlam, ht45, u4ehi4]
        · linarith only [h16, hlam, ht45, u4ehi4]
      · rcases h5emax with h22 | h22 | h22 | h22 | h22
        · linarith only [h0, h15, h22, hlam, ht45, u4ehi3]
        · linarith only [h1, h22, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h1, h22, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h15, h22, hlam, ht45, u4ehi3]
        · linarith only [h15, h22, hlam, ht45, u4ehi3]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
      · rcases h5emax with h30 | h30 | h30 | h30 | h30
        · linarith only [h0, h30, hlam, ht45, u4ehi0]
        · linarith only [h28, h30, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h30, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h29, h30, hlam, ht45, u4ehi4]
        · linarith only [h30, hlam, ht45, u4ehi4]
      · rcases h5emax with h36 | h36 | h36 | h36 | h36
        · linarith only [h0, h36, hlam, ht45, u4ehi0]
        · linarith only [h28, h36, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h36, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h29, h36, hlam, ht45, u4ehi3]
        · linarith only [h0, h36, hlam, ht45, u4ehi0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
      · rcases h5emax with h43 | h43 | h43 | h43 | h43
        · linarith only [h0, h43, hlam, ht45, u4ehi0]
        · linarith only [h28, h43, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h28, h43, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h0, h42, h43, hlam, ht45, u4ehi0]
        · linarith only [h0, h43, hlam, ht45, u4ehi0]
      · rcases h5emax with h49 | h49 | h49 | h49 | h49
        · linarith only [h0, h49, hlam, ht45, u4ehi0]
        · linarith only [h28, h49, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h28, h49, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h42, h49, hlam, ht45, u4ehi3]
        · linarith only [h0, h49, hlam, ht45, u4ehi0]

theorem r1l7_12_14_25_L_R_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi3, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem r1l7_12_23_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
    · linarith only [h1, hc34, hlam, hphi, u3ehi2]
  · linarith only [h0, hc34, hlam, hphi, u3ehi1]

theorem r1l7_12_23_L_R_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  linarith only [hlam, hphi, ht23, u2ehi2, u3elo2]

theorem r1l7_12_24_L_0_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h2, h5, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · linarith only [h6, hc34, hlam, hphi, u4elo4]
            · linarith only [h5, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc13, hlam, hphi, ht34, u4elo3]
        · linarith only [h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h12, h14, h15, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h15, hc34, hlam, hphi, u4elo4]
            · linarith only [h14, h2, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h12, h13, h2, hc24, hlam, hphi, u4elo3]
        · linarith only [h12, hc12, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
              · linarith only [h0, h22, h24, h26, h27, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h27, hc34, hlam, hphi, u4elo4]
            · linarith only [h26, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h25, hc13, hlam, hphi, ht34, u4elo3]
        · linarith only [h0, h24, hc01, hlam, hphi, ht12, u2elo3]
      · linarith only [h0, h22, h23, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
    · linarith only [h22, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem r1l7_12_24_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi2]

theorem r1l7_12_24_L_R_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem r1l7_12_24_L_R_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
          · linarith only [h1, h5, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h5, hc45, hlam, hphi, u4ehi2]
      · linarith only [h2, hc45, hlam, hphi, u4ehi1]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
            · linarith only [h13, h15, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h12, h15, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · linarith only [h10, h12, h14, hlam]
        · linarith only [h0, h13, hc34, hlam, hphi, ht23, u2ehi1]
      · linarith only [h12, hc45, hlam, hphi, u4ehi1]

theorem r1l7_12_25_L_R_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem r1l7_12_25_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5bigk with h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc25, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, hphi, ht23, ht34, ht45, p4_1, u2ehi4, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc15, hlam, hphi, p4_1, u5elo2]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo2]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc35, hlam, hphi, ht23, p4_1, u2ehi4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h2, hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h2, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc45, hlam, hphi, ht23, ht34, p4_1, u2ehi4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h3, hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h3, hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h33 | h33
    · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
      · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
        · rcases h5bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hlam, p36_1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hc25, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hc05, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, hphi, ht23, ht34, ht45, p36_1, u2ehi4, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hc35, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hlam, p36_1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc15, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc35, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, h33, hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc35, hlam, hphi, ht23, p36_1, u2ehi4]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, h34, hc15, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h34, hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, h33, h34, hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc45, hlam, hphi, ht23, ht34, p36_1, u2ehi4]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, h33, h35, hlam, p36_1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h35, hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, h35, hc35, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
        · linarith only [h35, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h34, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
    · linarith only [h33, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_13_24_L_0_H_L (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h6, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h7, hc34, hlam, hphi, u4elo4]
              · linarith only [h6, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h5, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
              · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h13, h15, h16, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h16, hc34, hlam, hphi, u4elo4]
              · linarith only [h15, h3, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h13, h14, h3, hc24, hlam, hphi, u4elo3]
          · linarith only [h13, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h24, h26, h29, h30, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h30, hc34, hlam, hphi, u4elo4]
              · linarith only [h29, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h28, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h27, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h24, h26, hc13, hlam, hphi, u3elo2]
      · linarith only [h24, h25, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h38 | h38
      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
        · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                · linarith only [h24, h38, h40, h42, h43, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                · linarith only [h43, hc34, hlam, hphi, u4elo4]
              · linarith only [h24, h38, h40, h42, hc23, hc24, hlam, hphi, u3elo1, u4elo3]
            · linarith only [h24, h38, h40, h41, hc24, hlam, hphi, u4elo3]
          · linarith only [h24, h39, h40, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h38, h39, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
      · linarith only [h38, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem r1l7_13_24_L_0_H_R (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
    · linarith only [h2, hc45, hlam, hphi, u4ehi1]

end R2N4
