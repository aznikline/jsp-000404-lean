import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT3_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [hlam, hphi, ht34, ht45, u3ehi4, u5elo3]

theorem n7l_sBT3_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                · linarith only [h1, h4, h9, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h2, h4, h6, h7, hlam]
                  · linarith only [h11, h6, h7, hc23, hlam, hphi, u3elo4]
            · linarith only [h3, h4, h6, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
          · linarith only [h15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h15, h17, h3, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h15, h19, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                · linarith only [h15, h21, h3, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h15, h23, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi0]
                  · linarith only [h0, h23, h3, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
          · linarith only [h27, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
            · linarith only [h0, h2, h27, h29, hc23, hlam, hphi, u3elo4]
            · linarith only [h0, h2, h26, h27, h29, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h32 | h32
          · linarith only [h32, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · linarith only [h0, h26, h32, h34, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h26, h36, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                · linarith only [h1, h2, h32, h38, hlam]
                · linarith only [h1, h2, h34, h38, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
    · rcases m.htr 0 1 5 (by decide) (by decide) with h43 | h43
      · linarith only [h0, h43, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h45 | h45
        · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
          · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                · linarith only [h42, h43, h46, h50, hlam]
                · linarith only [h42, h43, h50, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                · linarith only [h0, h42, h46, h49, h53, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h42, h49, h53, hc13, hlam, hphi, u3elo4]
            · linarith only [h0, h42, h48, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h42, h45, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h58 | h58
      · linarith only [h42, h58, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h60 | h60
        · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
          · linarith only [h61, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
              · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                · linarith only [h42, h61, h65, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h42, h65, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                · linarith only [h68, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                · linarith only [h42, h68, hc01, hlam, hphi, ht12, ht23, u3elo4]
            · linarith only [h0, h63, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
          · linarith only [h72, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
            · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                · linarith only [h72, h76, hc03, hlam, hphi, u3elo1]
                · linarith only [h42, h76, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h0, h60, h74, h75, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h74, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem n7l_sBT3_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h24 | h24
    · rcases p0_3 (m.d 0 2) (by simp) with h25 | h25
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · rcases p0_3 (m.d 0 4) (by simp) with h27 | h27
          · linarith only [h27, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · rcases m.htr 0 1 2 (by decide) (by decide) with h30 | h30
              · linarith only [h25, h30, hlam]
              · linarith only [h30, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h29, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h26, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h35 | h35
        · rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
          · linarith only [h36, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · rcases m.htr 0 1 2 (by decide) (by decide) with h39 | h39
              · rcases m.htr 0 1 3 (by decide) (by decide) with h40 | h40
                · linarith only [h35, h40, hlam]
                · linarith only [h25, h40, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h25, h39, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h38, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h35, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h24, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h48 | h48
    · linarith only [h48, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h50 | h50
      · rcases p0_3 (m.d 0 3) (by simp) with h51 | h51
        · rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h54, hlam, p0_0]
              · linarith only [h54, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h53, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h58 | h58
            · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
              · linarith only [h59, hlam, p0_0]
              · linarith only [h59, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h58, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h51, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h50, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · rcases p0_3 (m.d 0 2) (by simp) with h68 | h68
      · rcases p0_3 (m.d 0 3) (by simp) with h69 | h69
        · rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
          · linarith only [h70, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h72 | h72
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · rcases m.htr 0 1 3 (by decide) (by decide) with h74 | h74
                · rcases m.htr 0 1 4 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h77 | h77
                      · linarith only [h69, h77, hlam]
                      · linarith only [h77, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h73, h75, h76, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h73, h75, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h73, h74, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h67, h73, hlam]
            · linarith only [h72, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h69, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h87 | h87
      · rcases p0_3 (m.d 0 3) (by simp) with h88 | h88
        · rcases p0_3 (m.d 0 4) (by simp) with h89 | h89
          · linarith only [h89, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h91 | h91
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · linarith only [h67, h92, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h67, h92, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h91, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h88, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h87, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h99 | h99
    · linarith only [h99, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h101 | h101
      · rcases p0_3 (m.d 0 3) (by simp) with h102 | h102
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · rcases m.htr 0 1 2 (by decide) (by decide) with h105 | h105
              · linarith only [h105, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h105, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h101, h104, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h109 | h109
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · linarith only [h101, h110, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h110, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h101, h109, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h102, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h115 | h115
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 0 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h118, hlam]
            · linarith only [h117, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h122 | h122
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · linarith only [h123, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h123, hlam]
            · linarith only [h122, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h115, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h128 | h128
    · rcases p0_3 (m.d 0 2) (by simp) with h129 | h129
      · linarith only [h129, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h131 | h131
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 0 5) (by simp) with h133 | h133
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · rcases m.htr 0 1 3 (by decide) (by decide) with h135 | h135
                · rcases m.htr 0 1 4 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h137 | h137
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h138 | h138
                      · linarith only [h138, hlam, p0_0]
                      · linarith only [h138, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h134, h135, h137, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h134, h135, h136, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h128, h135, hlam]
              · linarith only [h128, h134, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h128, h133, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 1 3 (by decide) (by decide) with h148 | h148
                · rcases m.htr 0 1 4 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h151 | h151
                      · linarith only [h151, hlam, p0_0]
                      · linarith only [h151, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h147, h148, h150, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h147, h148, h149, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h128, h148, hlam]
              · linarith only [h128, h147, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h128, h146, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h131, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h160 | h160
      · linarith only [h160, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 0 5) (by simp) with h164 | h164
            · rcases m.htr 0 1 2 (by decide) (by decide) with h165 | h165
              · linarith only [h128, h165, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h167 | h167
                · linarith only [h165, h167, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h165, h167, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h164, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h171 | h171
            · rcases m.htr 0 1 2 (by decide) (by decide) with h172 | h172
              · linarith only [h128, h172, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
                · linarith only [h172, h174, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h172, h174, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h171, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h162, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h180 | h180
    · rcases p0_3 (m.d 0 2) (by simp) with h181 | h181
      · rcases p0_3 (m.d 0 3) (by simp) with h182 | h182
        · rcases p0_3 (m.d 0 4) (by simp) with h183 | h183
          · linarith only [h183, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · rcases m.htr 0 1 2 (by decide) (by decide) with h186 | h186
              · rcases m.htr 0 1 3 (by decide) (by decide) with h187 | h187
                · rcases m.htr 0 1 4 (by decide) (by decide) with h188 | h188
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h189 | h189
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h190 | h190
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h191 | h191
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h192 | h192
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
                            · linarith only [h186, h190, h193, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h193, hlam, p0_0]
                          · linarith only [h190, h192, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                        · linarith only [h188, h190, h191, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h181, h190, hlam]
                    · linarith only [h187, h188, h189, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h187, h188, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h180, h187, hlam]
              · linarith only [h180, h186, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h180, h185, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h182, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h205 | h205
        · rcases p0_3 (m.d 0 4) (by simp) with h206 | h206
          · linarith only [h206, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h208 | h208
            · rcases m.htr 0 1 2 (by decide) (by decide) with h209 | h209
              · rcases m.htr 0 1 3 (by decide) (by decide) with h210 | h210
                · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
                      · linarith only [h181, h210, h213, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h181, h209, h213, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h181, h209, h210, h212, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h181, h209, h210, h211, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h180, h210, hlam]
              · linarith only [h180, h181, h209, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h180, h208, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h205, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h222 | h222
      · rcases p0_3 (m.d 0 3) (by simp) with h223 | h223
        · rcases p0_3 (m.d 0 4) (by simp) with h224 | h224
          · linarith only [h224, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h226 | h226
            · rcases m.htr 0 1 2 (by decide) (by decide) with h227 | h227
              · linarith only [h180, h227, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h180, h222, h227, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h222, h226, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h223, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h232 | h232
        · rcases p0_3 (m.d 0 4) (by simp) with h233 | h233
          · linarith only [h233, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h235 | h235
            · rcases m.htr 0 1 2 (by decide) (by decide) with h236 | h236
              · linarith only [h180, h236, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h238 | h238
                · linarith only [h222, h236, h238, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h222, h236, h238, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h235, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h232, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h244 | h244
    · linarith only [h244, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h246 | h246
      · rcases p0_3 (m.d 0 3) (by simp) with h247 | h247
        · rcases p0_3 (m.d 0 4) (by simp) with h248 | h248
          · rcases p0_3 (m.d 0 5) (by simp) with h249 | h249
            · rcases m.htr 0 1 2 (by decide) (by decide) with h250 | h250
              · linarith only [h246, h250, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h246, h250, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h246, h249, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h248, hlam, p0_0]
        · linarith only [h246, h247, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h256 | h256
        · rcases p0_3 (m.d 0 4) (by simp) with h257 | h257
          · rcases p0_3 (m.d 0 5) (by simp) with h258 | h258
            · rcases m.htr 0 1 2 (by decide) (by decide) with h259 | h259
              · linarith only [h256, h259, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h246, h259, hlam]
            · linarith only [h258, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h257, hlam, p0_0]
        · linarith only [h256, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h265 | h265
    · rcases p0_3 (m.d 0 2) (by simp) with h266 | h266
      · linarith only [h266, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h268 | h268
        · rcases p0_3 (m.d 0 4) (by simp) with h269 | h269
          · rcases p0_3 (m.d 0 5) (by simp) with h270 | h270
            · rcases m.htr 0 1 2 (by decide) (by decide) with h271 | h271
              · rcases m.htr 0 1 3 (by decide) (by decide) with h272 | h272
                · rcases m.htr 0 1 4 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h274 | h274
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h275 | h275
                      · linarith only [h268, h272, h275, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h268, h275, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h271, h273, h274, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h265, h273, hlam]
                · linarith only [h265, h271, h272, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h265, h271, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h265, h270, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h269, hlam, p0_0]
        · linarith only [h265, h268, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h285 | h285
      · linarith only [h285, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h287 | h287
        · rcases p0_3 (m.d 0 4) (by simp) with h288 | h288
          · rcases p0_3 (m.d 0 5) (by simp) with h289 | h289
            · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
              · linarith only [h265, h290, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h292 | h292
                · linarith only [h287, h290, h292, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h287, h290, h292, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h287, h289, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h288, hlam, p0_0]
        · linarith only [h287, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h301 | h301
    · linarith only [h301, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h303 | h303
      · rcases p0_3 (m.d 0 3) (by simp) with h304 | h304
        · rcases p0_3 (m.d 0 4) (by simp) with h305 | h305
          · rcases p0_3 (m.d 0 5) (by simp) with h306 | h306
            · rcases m.htr 0 1 2 (by decide) (by decide) with h307 | h307
              · linarith only [h307, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h303, h307, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h311 | h311
            · rcases m.htr 0 1 2 (by decide) (by decide) with h312 | h312
              · linarith only [h303, h312, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h303, h312, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h311, hlam, p0_0]
        · linarith only [h303, h304, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h317 | h317
        · rcases p0_3 (m.d 0 4) (by simp) with h318 | h318
          · rcases p0_3 (m.d 0 5) (by simp) with h319 | h319
            · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
              · linarith only [h320, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h303, h320, hlam]
            · linarith only [h319, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h324 | h324
            · rcases m.htr 0 1 2 (by decide) (by decide) with h325 | h325
              · linarith only [h325, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h303, h325, hlam]
            · linarith only [h324, hlam, p0_0]
        · linarith only [h317, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h330 | h330
    · rcases p0_3 (m.d 0 2) (by simp) with h331 | h331
      · linarith only [h331, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h333 | h333
        · rcases p0_3 (m.d 0 4) (by simp) with h334 | h334
          · rcases p0_3 (m.d 0 5) (by simp) with h335 | h335
            · rcases m.htr 0 1 2 (by decide) (by decide) with h336 | h336
              · rcases m.htr 0 1 3 (by decide) (by decide) with h337 | h337
                · rcases m.htr 0 1 4 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h340 | h340
                      · linarith only [h333, h337, h340, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h333, h340, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h330, h339, hlam]
                  · linarith only [h330, h336, h338, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h330, h336, h337, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h330, h336, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h335, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h348 | h348
            · rcases m.htr 0 1 2 (by decide) (by decide) with h349 | h349
              · rcases m.htr 0 1 3 (by decide) (by decide) with h350 | h350
                · rcases m.htr 0 1 4 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h353 | h353
                      · linarith only [h333, h350, h353, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h333, h353, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h330, h352, hlam]
                  · linarith only [h333, h349, h350, h351, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h330, h349, h350, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h330, h349, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h348, hlam, p0_0]
        · linarith only [h330, h333, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h362 | h362
      · linarith only [h362, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h364 | h364
        · rcases p0_3 (m.d 0 4) (by simp) with h365 | h365
          · rcases p0_3 (m.d 0 5) (by simp) with h366 | h366
            · rcases m.htr 0 1 2 (by decide) (by decide) with h367 | h367
              · linarith only [h330, h367, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h369 | h369
                · linarith only [h367, h369, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h364, h367, h369, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h366, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h373 | h373
            · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
              · linarith only [h330, h374, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h376 | h376
                · linarith only [h374, h376, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h364, h374, h376, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h373, hlam, p0_0]
        · linarith only [h364, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h382 | h382
    · rcases p0_3 (m.d 0 2) (by simp) with h383 | h383
      · rcases p0_3 (m.d 0 3) (by simp) with h384 | h384
        · rcases p0_3 (m.d 0 4) (by simp) with h385 | h385
          · linarith only [h385, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h387 | h387
            · rcases m.htr 0 1 2 (by decide) (by decide) with h388 | h388
              · rcases m.htr 0 1 3 (by decide) (by decide) with h389 | h389
                · rcases m.htr 0 1 4 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h391 | h391
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h392 | h392
                      · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
                        · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
                          · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
                            · linarith only [h384, h388, h392, h395, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h384, h395, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                          · linarith only [h383, h394, hlam]
                        · linarith only [h384, h390, h392, h393, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h383, h390, h392, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h382, h391, hlam]
                  · linarith only [h382, h390, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h383, h388, h389, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h382, h388, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h387, hlam, p0_0]
        · linarith only [h382, h384, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h407 | h407
        · rcases p0_3 (m.d 0 4) (by simp) with h408 | h408
          · linarith only [h408, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h410 | h410
            · rcases m.htr 0 1 2 (by decide) (by decide) with h411 | h411
              · rcases m.htr 0 1 3 (by decide) (by decide) with h412 | h412
                · rcases m.htr 0 1 4 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h415 | h415
                      · linarith only [h383, h407, h412, h415, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h383, h407, h411, h415, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h382, h414, hlam]
                  · linarith only [h383, h407, h411, h412, h413, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h382, h383, h411, h412, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h382, h383, h411, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h410, hlam, p0_0]
        · linarith only [h382, h407, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h424 | h424
      · rcases p0_3 (m.d 0 3) (by simp) with h425 | h425
        · rcases p0_3 (m.d 0 4) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · rcases m.htr 0 1 2 (by decide) (by decide) with h429 | h429
              · linarith only [h382, h429, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h382, h424, h429, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h428, hlam, p0_0]
        · linarith only [h424, h425, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h434 | h434
        · rcases p0_3 (m.d 0 4) (by simp) with h435 | h435
          · linarith only [h435, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h437 | h437
            · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
              · linarith only [h382, h438, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h440 | h440
                · linarith only [h424, h438, h440, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h424, h434, h438, h440, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h437, hlam, p0_0]
        · linarith only [h434, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.2.1
  have h3ehi := hb3.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
                · linarith only [h16, h5, hlam]
                · linarith only [h16, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h15, hlam, p0_0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h24 | h24
    · rcases p0_3 (m.d 0 2) (by simp) with h25 | h25
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · rcases p0_3 (m.d 0 4) (by simp) with h27 | h27
          · linarith only [h27, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · rcases m.htr 0 1 2 (by decide) (by decide) with h30 | h30
              · linarith only [h25, h30, hlam]
              · linarith only [h30, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h29, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h26, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h35 | h35
        · rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
          · linarith only [h36, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · rcases m.htr 0 1 2 (by decide) (by decide) with h39 | h39
              · rcases m.htr 0 1 3 (by decide) (by decide) with h40 | h40
                · linarith only [h35, h40, hlam]
                · linarith only [h25, h40, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h25, h39, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h38, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h35, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h24, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h48 | h48
    · linarith only [h48, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h50 | h50
      · rcases p0_3 (m.d 0 3) (by simp) with h51 | h51
        · rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h54, hlam, p0_0]
              · linarith only [h54, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h53, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h58 | h58
            · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
              · linarith only [h59, hlam, p0_0]
              · linarith only [h59, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h58, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h51, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h50, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · rcases p0_3 (m.d 0 2) (by simp) with h68 | h68
      · rcases p0_3 (m.d 0 3) (by simp) with h69 | h69
        · rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
          · linarith only [h70, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h72 | h72
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · rcases m.htr 0 1 3 (by decide) (by decide) with h74 | h74
                · rcases m.htr 0 1 4 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h77 | h77
                      · linarith only [h69, h77, hlam]
                      · linarith only [h77, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h73, h75, h76, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h73, h75, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h73, h74, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h67, h73, hlam]
            · linarith only [h72, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h69, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h87 | h87
      · rcases p0_3 (m.d 0 3) (by simp) with h88 | h88
        · rcases p0_3 (m.d 0 4) (by simp) with h89 | h89
          · linarith only [h89, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h91 | h91
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · linarith only [h67, h92, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h67, h92, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h91, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h88, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h87, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h99 | h99
    · linarith only [h99, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h101 | h101
      · rcases p0_3 (m.d 0 3) (by simp) with h102 | h102
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · rcases m.htr 0 1 2 (by decide) (by decide) with h105 | h105
              · linarith only [h105, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h105, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h101, h104, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h109 | h109
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · linarith only [h101, h110, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h110, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h101, h109, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h102, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h115 | h115
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · rcases p0_3 (m.d 0 5) (by simp) with h117 | h117
            · rcases m.htr 0 1 2 (by decide) (by decide) with h118 | h118
              · linarith only [h118, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h118, hlam]
            · linarith only [h117, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h122 | h122
            · rcases m.htr 0 1 2 (by decide) (by decide) with h123 | h123
              · linarith only [h123, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h101, h123, hlam]
            · linarith only [h122, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h115, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h128 | h128
    · rcases p0_3 (m.d 0 2) (by simp) with h129 | h129
      · linarith only [h129, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h131 | h131
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · rcases p0_3 (m.d 0 5) (by simp) with h133 | h133
            · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
              · rcases m.htr 0 1 3 (by decide) (by decide) with h135 | h135
                · rcases m.htr 0 1 4 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h137 | h137
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h138 | h138
                      · linarith only [h138, hlam, p0_0]
                      · linarith only [h138, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h134, h135, h137, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h134, h135, h136, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h128, h135, hlam]
              · linarith only [h128, h134, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h128, h133, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 1 3 (by decide) (by decide) with h148 | h148
                · rcases m.htr 0 1 4 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h151 | h151
                      · linarith only [h151, hlam, p0_0]
                      · linarith only [h151, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h147, h148, h150, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h147, h148, h149, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h128, h148, hlam]
              · linarith only [h128, h147, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h128, h146, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h131, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h160 | h160
      · linarith only [h160, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 0 5) (by simp) with h164 | h164
            · rcases m.htr 0 1 2 (by decide) (by decide) with h165 | h165
              · linarith only [h128, h165, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h167 | h167
                · linarith only [h165, h167, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h165, h167, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h164, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h171 | h171
            · rcases m.htr 0 1 2 (by decide) (by decide) with h172 | h172
              · linarith only [h128, h172, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
                · linarith only [h172, h174, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h172, h174, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h171, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h162, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h180 | h180
    · rcases p0_3 (m.d 0 2) (by simp) with h181 | h181
      · rcases p0_3 (m.d 0 3) (by simp) with h182 | h182
        · rcases p0_3 (m.d 0 4) (by simp) with h183 | h183
          · linarith only [h183, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · rcases m.htr 0 1 2 (by decide) (by decide) with h186 | h186
              · rcases m.htr 0 1 3 (by decide) (by decide) with h187 | h187
                · rcases m.htr 0 1 4 (by decide) (by decide) with h188 | h188
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h189 | h189
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h190 | h190
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
                          · linarith only [h186, h190, h192, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                          · linarith only [h192, hlam, p0_0]
                        · linarith only [h190, h191, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                      · linarith only [h181, h190, hlam]
                    · linarith only [h187, h188, h189, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                  · linarith only [h187, h188, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h180, h187, hlam]
              · linarith only [h180, h186, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h180, h185, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h182, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h203 | h203
        · rcases p0_3 (m.d 0 4) (by simp) with h204 | h204
          · linarith only [h204, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h206 | h206
            · rcases m.htr 0 1 2 (by decide) (by decide) with h207 | h207
              · rcases m.htr 0 1 3 (by decide) (by decide) with h208 | h208
                · rcases m.htr 0 1 4 (by decide) (by decide) with h209 | h209
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
                      · linarith only [h181, h208, h211, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h181, h207, h211, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h181, h207, h208, h210, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h181, h207, h208, h209, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h180, h208, hlam]
              · linarith only [h180, h181, h207, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h180, h206, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h203, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h220 | h220
      · rcases p0_3 (m.d 0 3) (by simp) with h221 | h221
        · rcases p0_3 (m.d 0 4) (by simp) with h222 | h222
          · linarith only [h222, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h224 | h224
            · rcases m.htr 0 1 2 (by decide) (by decide) with h225 | h225
              · linarith only [h180, h225, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h180, h220, h225, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h220, h224, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h221, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h230 | h230
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · linarith only [h231, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h233 | h233
            · rcases m.htr 0 1 2 (by decide) (by decide) with h234 | h234
              · linarith only [h180, h234, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h236 | h236
                · linarith only [h220, h234, h236, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h220, h234, h236, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h233, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h230, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h242 | h242
    · linarith only [h242, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h244 | h244
      · rcases p0_3 (m.d 0 3) (by simp) with h245 | h245
        · rcases p0_3 (m.d 0 4) (by simp) with h246 | h246
          · rcases p0_3 (m.d 0 5) (by simp) with h247 | h247
            · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
              · linarith only [h244, h248, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h244, h248, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h244, h247, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h246, hlam, p0_0]
        · linarith only [h244, h245, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h254 | h254
        · rcases p0_3 (m.d 0 4) (by simp) with h255 | h255
          · rcases p0_3 (m.d 0 5) (by simp) with h256 | h256
            · rcases m.htr 0 1 2 (by decide) (by decide) with h257 | h257
              · linarith only [h254, h257, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h244, h257, hlam]
            · linarith only [h254, h256, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h255, hlam, p0_0]
        · linarith only [h254, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h263 | h263
    · rcases p0_3 (m.d 0 2) (by simp) with h264 | h264
      · linarith only [h264, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h266 | h266
        · rcases p0_3 (m.d 0 4) (by simp) with h267 | h267
          · rcases p0_3 (m.d 0 5) (by simp) with h268 | h268
            · rcases m.htr 0 1 2 (by decide) (by decide) with h269 | h269
              · rcases m.htr 0 1 3 (by decide) (by decide) with h270 | h270
                · rcases m.htr 0 1 4 (by decide) (by decide) with h271 | h271
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h273 | h273
                      · linarith only [h266, h270, h273, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h266, h273, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h269, h271, h272, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                  · linarith only [h263, h271, hlam]
                · linarith only [h263, h269, h270, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h263, h269, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h263, h268, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h267, hlam, p0_0]
        · linarith only [h263, h266, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h283 | h283
      · linarith only [h283, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
          · rcases p0_3 (m.d 0 5) (by simp) with h287 | h287
            · rcases m.htr 0 1 2 (by decide) (by decide) with h288 | h288
              · linarith only [h263, h288, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h290 | h290
                · linarith only [h285, h288, h290, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h285, h288, h290, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h285, h287, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h286, hlam, p0_0]
        · linarith only [h285, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h299 | h299
    · linarith only [h299, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h301 | h301
      · rcases p0_3 (m.d 0 3) (by simp) with h302 | h302
        · rcases p0_3 (m.d 0 4) (by simp) with h303 | h303
          · rcases p0_3 (m.d 0 5) (by simp) with h304 | h304
            · rcases m.htr 0 1 2 (by decide) (by decide) with h305 | h305
              · linarith only [h301, h305, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h305, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h304, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h309 | h309
            · rcases m.htr 0 1 2 (by decide) (by decide) with h310 | h310
              · linarith only [h301, h310, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h310, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h309, hlam, p0_0]
        · linarith only [h301, h302, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h315 | h315
        · rcases p0_3 (m.d 0 4) (by simp) with h316 | h316
          · rcases p0_3 (m.d 0 5) (by simp) with h317 | h317
            · rcases m.htr 0 1 2 (by decide) (by decide) with h318 | h318
              · linarith only [h318, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h318, hlam]
            · linarith only [h317, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h322 | h322
            · rcases m.htr 0 1 2 (by decide) (by decide) with h323 | h323
              · linarith only [h323, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h301, h323, hlam]
            · linarith only [h322, hlam, p0_0]
        · linarith only [h315, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h328 | h328
    · rcases p0_3 (m.d 0 2) (by simp) with h329 | h329
      · linarith only [h329, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h331 | h331
        · rcases p0_3 (m.d 0 4) (by simp) with h332 | h332
          · rcases p0_3 (m.d 0 5) (by simp) with h333 | h333
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · rcases m.htr 0 1 3 (by decide) (by decide) with h335 | h335
                · rcases m.htr 0 1 4 (by decide) (by decide) with h336 | h336
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h337 | h337
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h338 | h338
                      · linarith only [h331, h335, h338, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h331, h338, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h328, h337, hlam]
                  · linarith only [h328, h334, h336, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h328, h334, h335, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h328, h334, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h333, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h346 | h346
            · rcases m.htr 0 1 2 (by decide) (by decide) with h347 | h347
              · rcases m.htr 0 1 3 (by decide) (by decide) with h348 | h348
                · rcases m.htr 0 1 4 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h351 | h351
                      · linarith only [h331, h348, h351, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h331, h351, hc02, hc23, hlam, hphi, p0_1]
                    · linarith only [h328, h350, hlam]
                  · linarith only [h331, h347, h348, h349, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h328, h347, h348, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h328, h347, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h346, hlam, p0_0]
        · linarith only [h328, h331, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h360 | h360
      · linarith only [h360, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h362 | h362
        · rcases p0_3 (m.d 0 4) (by simp) with h363 | h363
          · rcases p0_3 (m.d 0 5) (by simp) with h364 | h364
            · rcases m.htr 0 1 2 (by decide) (by decide) with h365 | h365
              · linarith only [h328, h365, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h367 | h367
                · linarith only [h365, h367, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h362, h365, h367, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h364, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h371 | h371
            · rcases m.htr 0 1 2 (by decide) (by decide) with h372 | h372
              · linarith only [h328, h372, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h374 | h374
                · linarith only [h372, h374, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h362, h372, h374, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h371, hlam, p0_0]
        · linarith only [h362, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h380 | h380
    · rcases p0_3 (m.d 0 2) (by simp) with h381 | h381
      · rcases p0_3 (m.d 0 3) (by simp) with h382 | h382
        · rcases p0_3 (m.d 0 4) (by simp) with h383 | h383
          · linarith only [h383, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h385 | h385
            · rcases m.htr 0 1 2 (by decide) (by decide) with h386 | h386
              · rcases m.htr 0 1 3 (by decide) (by decide) with h387 | h387
                · rcases m.htr 0 1 4 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h390 | h390
                      · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
                          · linarith only [h382, h386, h390, h392, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                          · linarith only [h382, h392, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1]
                        · linarith only [h381, h391, hlam]
                      · linarith only [h381, h388, h390, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                    · linarith only [h380, h389, hlam]
                  · linarith only [h380, h388, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h381, h386, h387, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h380, h386, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h385, hlam, p0_0]
        · linarith only [h380, h382, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h403 | h403
        · rcases p0_3 (m.d 0 4) (by simp) with h404 | h404
          · linarith only [h404, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h406 | h406
            · rcases m.htr 0 1 2 (by decide) (by decide) with h407 | h407
              · rcases m.htr 0 1 3 (by decide) (by decide) with h408 | h408
                · rcases m.htr 0 1 4 (by decide) (by decide) with h409 | h409
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h410 | h410
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h411 | h411
                      · linarith only [h381, h403, h408, h411, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h381, h403, h407, h411, hc12, hc23, hlam, hphi, p0_1]
                    · linarith only [h380, h410, hlam]
                  · linarith only [h381, h403, h407, h408, h409, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
                · linarith only [h380, h381, h407, h408, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h380, h381, h407, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h406, hlam, p0_0]
        · linarith only [h380, h403, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h420 | h420
      · rcases p0_3 (m.d 0 3) (by simp) with h421 | h421
        · rcases p0_3 (m.d 0 4) (by simp) with h422 | h422
          · linarith only [h422, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h424 | h424
            · rcases m.htr 0 1 2 (by decide) (by decide) with h425 | h425
              · linarith only [h380, h425, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h380, h420, h425, hc01, hc12, hlam, hphi, p0_1]
            · linarith only [h424, hlam, p0_0]
        · linarith only [h420, h421, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h430 | h430
        · rcases p0_3 (m.d 0 4) (by simp) with h431 | h431
          · linarith only [h431, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h433 | h433
            · rcases m.htr 0 1 2 (by decide) (by decide) with h434 | h434
              · linarith only [h380, h434, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h436 | h436
                · linarith only [h420, h434, h436, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h420, h430, h434, h436, hc01, hc13, hlam, hphi, p0_1]
            · linarith only [h433, hlam, p0_0]
        · linarith only [h430, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3ehi := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3elo := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · linarith only [h5, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h8, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
            · linarith only [h11, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h15 | h15
    · rcases p0_3 (m.d 0 2) (by simp) with h16 | h16
      · rcases p0_3 (m.d 0 3) (by simp) with h17 | h17
        · linarith only [h17, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 0 5) (by simp) with h20 | h20
            · linarith only [h20, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h20, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
            · linarith only [h23, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h23, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h16, h29, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
            · linarith only [h32, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h32, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · rcases p0_3 (m.d 0 2) (by simp) with h37 | h37
      · rcases p0_3 (m.d 0 3) (by simp) with h38 | h38
        · linarith only [h38, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h40 | h40
          · linarith only [h40, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
            · linarith only [h38, h42, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h42, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h45 | h45
        · linarith only [h37, h45, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h47 | h47
          · linarith only [h47, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h49 | h49
            · linarith only [h37, h49, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h49, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h54 | h54
    · linarith only [h54, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h56 | h56
      · rcases p0_3 (m.d 0 3) (by simp) with h57 | h57
        · linarith only [h57, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 0 5) (by simp) with h60 | h60
            · linarith only [h60, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h60, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · linarith only [h63, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h63, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h56, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · rcases p0_3 (m.d 0 2) (by simp) with h69 | h69
      · rcases p0_3 (m.d 0 3) (by simp) with h70 | h70
        · linarith only [h70, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · linarith only [h73, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h68, h73, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h76 | h76
            · linarith only [h76, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h76, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h80 | h80
      · rcases p0_3 (m.d 0 3) (by simp) with h81 | h81
        · linarith only [h81, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 0 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h84, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h87 | h87
            · linarith only [h87, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h87, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h80, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h91 | h91
    · rcases p0_3 (m.d 0 2) (by simp) with h92 | h92
      · rcases p0_3 (m.d 0 3) (by simp) with h93 | h93
        · linarith only [h93, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h95 | h95
          · linarith only [h95, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h97 | h97
            · linarith only [h93, h97, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h91, h97, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h92, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h101 | h101
      · rcases p0_3 (m.d 0 3) (by simp) with h102 | h102
        · linarith only [h102, h91, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h104 | h104
          · linarith only [h104, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h106 | h106
            · linarith only [h106, h91, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h106, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h101, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h116 | h116
    · linarith only [h116, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h118 | h118
      · rcases p0_3 (m.d 0 3) (by simp) with h119 | h119
        · linarith only [h119, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 0 5) (by simp) with h122 | h122
            · linarith only [h122, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h118, h122, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · linarith only [h126, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · linarith only [h129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h129, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h128, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h133 | h133
    · rcases p0_3 (m.d 0 2) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h136 | h136
        · linarith only [h136, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 0 5) (by simp) with h139 | h139
            · linarith only [h139, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h133, h139, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h143 | h143
      · linarith only [h143, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h145 | h145
        · linarith only [h133, h145, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 0 5) (by simp) with h148 | h148
            · linarith only [h133, h148, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h148, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h147, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h152 | h152
    · rcases p0_3 (m.d 0 2) (by simp) with h153 | h153
      · rcases p0_3 (m.d 0 3) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 0 5) (by simp) with h157 | h157
            · linarith only [h157, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h152, h157, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h161 | h161
        · linarith only [h161, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 0 5) (by simp) with h164 | h164
            · linarith only [h153, h164, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h164, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h168 | h168
      · rcases p0_3 (m.d 0 3) (by simp) with h169 | h169
        · linarith only [h169, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 0 5) (by simp) with h172 | h172
            · linarith only [h152, h172, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h168, h172, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h176 | h176
        · linarith only [h176, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h178 | h178
          · rcases p0_3 (m.d 0 5) (by simp) with h179 | h179
            · linarith only [h168, h179, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h179, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h178, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · linarith only [h7, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h10 | h10
            · linarith only [h10, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h10, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · linarith only [h14, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h14, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h17 | h17
            · linarith only [h17, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h17, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · rcases p0_3 (m.d 0 2) (by simp) with h22 | h22
      · rcases p0_3 (m.d 0 3) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
            · linarith only [h26, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h26, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h29, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 0 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h35, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · linarith only [h38, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h38, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h42 | h42
    · rcases p0_3 (m.d 0 2) (by simp) with h43 | h43
      · rcases p0_3 (m.d 0 3) (by simp) with h44 | h44
        · rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · linarith only [h47, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h47, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h52, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h55 | h55
        · rcases p0_3 (m.d 0 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h58, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · linarith only [h55, h63, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h63, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h70 | h70
      · rcases p0_3 (m.d 0 3) (by simp) with h71 | h71
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · linarith only [h73, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h73, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h76 | h76
            · linarith only [h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h76, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 0 5) (by simp) with h80 | h80
            · linarith only [h80, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h80, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h83 | h83
            · linarith only [h83, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h83, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h88 | h88
    · rcases p0_3 (m.d 0 2) (by simp) with h89 | h89
      · rcases p0_3 (m.d 0 3) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 0 5) (by simp) with h93 | h93
            · linarith only [h93, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h88, h93, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h96 | h96
            · linarith only [h96, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h88, h96, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · rcases p0_3 (m.d 0 3) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h104, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · linarith only [h107, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h107, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h111 | h111
    · rcases p0_3 (m.d 0 2) (by simp) with h112 | h112
      · rcases p0_3 (m.d 0 3) (by simp) with h113 | h113
        · rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h116 | h116
            · linarith only [h116, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h111, h116, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h111, h121, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h125 | h125
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h129, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · linarith only [h126, h134, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h141 | h141
      · rcases p0_3 (m.d 0 3) (by simp) with h142 | h142
        · rcases p0_3 (m.d 0 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 0 5) (by simp) with h144 | h144
            · linarith only [h144, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h144, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h147, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h151 | h151
        · rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · linarith only [h153, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h153, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h156 | h156
            · linarith only [h156, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h156, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h163 | h163
        · rcases p0_3 (m.d 0 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
            · linarith only [h165, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h160, h165, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
            · linarith only [h168, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h168, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h174 | h174
        · rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h176, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h179 | h179
            · linarith only [h179, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h179, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h184 | h184
    · rcases p0_3 (m.d 0 2) (by simp) with h185 | h185
      · rcases p0_3 (m.d 0 3) (by simp) with h186 | h186
        · rcases p0_3 (m.d 0 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h189 | h189
            · linarith only [h189, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h184, h189, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h193 | h193
        · rcases p0_3 (m.d 0 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h184, h196, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h200 | h200
      · rcases p0_3 (m.d 0 3) (by simp) with h201 | h201
        · rcases p0_3 (m.d 0 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h200, h204, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h208 | h208
        · rcases p0_3 (m.d 0 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h211 | h211
            · linarith only [h200, h211, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h211, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h218 | h218
      · rcases p0_3 (m.d 0 3) (by simp) with h219 | h219
        · rcases p0_3 (m.d 0 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 0 5) (by simp) with h221 | h221
            · linarith only [h221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h218, h221, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 0 5) (by simp) with h226 | h226
            · linarith only [h226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h226, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h230 | h230
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · linarith only [h232, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h230, h232, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 0 5) (by simp) with h237 | h237
            · linarith only [h237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h237, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h241 | h241
    · rcases p0_3 (m.d 0 2) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 0 5) (by simp) with h246 | h246
            · linarith only [h246, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h241, h246, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 0 5) (by simp) with h251 | h251
            · linarith only [h251, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h241, h251, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h257 | h257
        · rcases p0_3 (m.d 0 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 0 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h257, h259, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · linarith only [h264, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h264, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h268 | h268
    · rcases p0_3 (m.d 0 2) (by simp) with h269 | h269
      · rcases p0_3 (m.d 0 3) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 0 5) (by simp) with h273 | h273
            · linarith only [h273, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h268, h273, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 0 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h268, h280, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h284 | h284
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 0 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h284, h288, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · linarith only [h284, h295, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h295, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · linarith only [h7, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h10 | h10
            · linarith only [h10, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h10, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · rcases p0_3 (m.d 0 2) (by simp) with h17 | h17
      · rcases p0_3 (m.d 0 3) (by simp) with h18 | h18
        · rcases p0_3 (m.d 0 4) (by simp) with h19 | h19
          · linarith only [h19, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h21 | h21
            · linarith only [h21, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h21, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h18, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h25 | h25
        · rcases p0_3 (m.d 0 4) (by simp) with h26 | h26
          · linarith only [h26, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h28 | h28
            · linarith only [h17, h28, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h28, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h25, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · linarith only [h16, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h36 | h36
      · rcases p0_3 (m.d 0 3) (by simp) with h37 | h37
        · rcases p0_3 (m.d 0 4) (by simp) with h38 | h38
          · rcases p0_3 (m.d 0 5) (by simp) with h39 | h39
            · linarith only [h39, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h39, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
            · linarith only [h42, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h42, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h37, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h49 | h49
    · rcases p0_3 (m.d 0 2) (by simp) with h50 | h50
      · rcases p0_3 (m.d 0 3) (by simp) with h51 | h51
        · rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
          · linarith only [h52, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h54 | h54
            · linarith only [h54, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h49, h54, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h51, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h50, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h59 | h59
      · rcases p0_3 (m.d 0 3) (by simp) with h60 | h60
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · linarith only [h49, h63, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h63, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h60, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h69 | h69
    · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h71 | h71
      · rcases p0_3 (m.d 0 3) (by simp) with h72 | h72
        · rcases p0_3 (m.d 0 4) (by simp) with h73 | h73
          · rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
            · linarith only [h74, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h74, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h77 | h77
            · linarith only [h77, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h77, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h72, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h81 | h81
        · rcases p0_3 (m.d 0 4) (by simp) with h82 | h82
          · rcases p0_3 (m.d 0 5) (by simp) with h83 | h83
            · linarith only [h83, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h83, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h86 | h86
            · linarith only [h86, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h86, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h81, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h90 | h90
    · rcases p0_3 (m.d 0 2) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h93 | h93
        · rcases p0_3 (m.d 0 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 0 5) (by simp) with h95 | h95
            · linarith only [h95, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h90, h95, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · linarith only [h98, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h90, h98, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h102 | h102
      · linarith only [h102, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h104 | h104
        · rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
          · rcases p0_3 (m.d 0 5) (by simp) with h106 | h106
            · linarith only [h106, h90, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h106, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h109 | h109
            · linarith only [h109, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h109, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h114 | h114
    · rcases p0_3 (m.d 0 2) (by simp) with h115 | h115
      · rcases p0_3 (m.d 0 3) (by simp) with h116 | h116
        · rcases p0_3 (m.d 0 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h119 | h119
            · linarith only [h119, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h114, h119, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h123 | h123
        · rcases p0_3 (m.d 0 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h114, h126, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h123, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h130 | h130
      · rcases p0_3 (m.d 0 3) (by simp) with h131 | h131
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · linarith only [h114, h134, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h130, h134, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h131, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h138 | h138
        · rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
          · linarith only [h139, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h141 | h141
            · linarith only [h130, h141, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h141, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h138, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h146 | h146
    · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h148 | h148
      · rcases p0_3 (m.d 0 3) (by simp) with h149 | h149
        · rcases p0_3 (m.d 0 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 0 5) (by simp) with h151 | h151
            · linarith only [h151, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h148, h151, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h150, hlam, p0_0]
        · linarith only [h148, h149, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h156 | h156
        · rcases p0_3 (m.d 0 4) (by simp) with h157 | h157
          · rcases p0_3 (m.d 0 5) (by simp) with h158 | h158
            · linarith only [h158, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h156, h158, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h157, hlam, p0_0]
        · linarith only [h156, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h163 | h163
    · rcases p0_3 (m.d 0 2) (by simp) with h164 | h164
      · linarith only [h164, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h166 | h166
        · rcases p0_3 (m.d 0 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
            · linarith only [h168, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h163, h168, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h167, hlam, p0_0]
        · linarith only [h163, h166, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
    · rcases p0_3 (m.d 0 2) (by simp) with h173 | h173
      · linarith only [h173, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h175 | h175
        · rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
          · rcases p0_3 (m.d 0 5) (by simp) with h177 | h177
            · linarith only [h163, h177, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h175, h177, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h176, hlam, p0_0]
        · linarith only [h175, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi0, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5bigk := hb5.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h1, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
              · linarith only [h7, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · linarith only [h0, h1, h6, h9, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h12 | h12
            · linarith only [h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14 | h14
              · linarith only [h12, h14, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · linarith only [h1, h14, h3, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h17 | h17
        · linarith only [h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h3, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h21 | h21
            · linarith only [h21, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h23 | h23
              · linarith only [h21, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h1, h17, h23, h25, h26, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h1, h21, h26, h28, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h28, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h1, h21, h31, h33, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h33, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h36 | h36
    · linarith only [h36, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
      · rcases m.htr 0 2 3 (by decide) (by decide) with h39 | h39
        · linarith only [h39, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h41 | h41
          · rcases m.htr 0 3 4 (by decide) (by decide) with h42 | h42
            · linarith only [h42, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
              · linarith only [h42, h44, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · linarith only [h0, h38, h39, h44, hlam]
          · linarith only [h0, h38, h41, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h48 | h48
        · linarith only [h48, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
          · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
            · linarith only [h51, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h53 | h53
              · linarith only [h51, h53, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · linarith only [h48, h50, h53, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
            · linarith only [h56, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
              · linarith only [h56, h58, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
                · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                          · linarith only [h0, h48, h56, h61, h65, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h48, h62, h65, hc01, hc13, hlam, hphi]
                        · linarith only [h60, h64, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h56, h62, h63, hc35, hlam, hphi, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
                      · linarith only [h62, h70, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                          · linarith only [h36, h62, h73, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h61, h70, h75, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                              · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h38, hlam, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h50, hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h58, hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht0b, ht5b, p78_1, u0elo4]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h38, h72, hc01, hc14, hlam, hphi, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h0, h48, h75, hc01, hc15, hlam, hphi, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h70, hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  rcases p78_3 (m.d 0 5) (by simp) with h88 | h88
                                  · linarith only [h38, h88, hlam]
                                  · linarith only [h60, h88, hlam]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h58, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p78_1, u3ehi0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h38, h75, h77, hc01, hc34, hlam, hphi, ht12, ht23, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h75, hlam, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  rcases p78_3 (m.d 0 5) (by simp) with h95 | h95
                                  · linarith only [h50, h95, hlam]
                                  · linarith only [h60, h95, hlam]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h58, h77, hc34, hlam, hphi, p78_1, u3ehi0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h0, h48, h61, h70, h77, hc01, hc34, hlam, hphi, ht12, ht23, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h0, h50, h77, hc01, hc34, hlam, hphi, ht12, ht23, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  rcases p78_3 (m.d 0 5) (by simp) with h102 | h102
                                  · linarith only [h102, h58, hlam]
                                  · linarith only [h102, h60, hlam]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h60, hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h72, hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h0, h48, h75, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p78_1]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [h77, hlam, p78_0]
                                · have p78_0 := h78c.1
                                  have p78_1 := h78c.2.1
                                  have p78_2 := h78c.2.2.1
                                  have p78_3 := h78c.2.2.2
                                  linarith only [hlam, p78_0]
                              · linarith only [h60, h62, h77, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h48, h60, h61, h62, h72, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h114 | h114
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                              · rcases h5bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h38, hlam, p118_1]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h50, hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h58, hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht0b, ht5b, p118_1, u0elo4]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h114, h38, hc01, hc14, hlam, hphi, p118_1]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h112, h114, h116, h58, h61, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h112, h114, h58, h61, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  rcases p118_3 (m.d 0 5) (by simp) with h128 | h128
                                  · linarith only [h128, h38, hlam]
                                  · linarith only [h128, h60, hlam]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h58, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h116, h38, hc01, hc23, hlam, hphi, ht12, p118_1]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h116, h58, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  rcases p118_3 (m.d 0 5) (by simp) with h135 | h135
                                  · linarith only [h135, h50, hlam]
                                  · linarith only [h135, h60, hlam]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h113, h58, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p118_1, u3ehi0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h113, hlam, p118_1]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h116, hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h112, h117, h61, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p118_1]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h60, hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h114, hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h0, h50, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p118_1]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [h117, hlam, p118_0]
                                · have p118_0 := h118c.1
                                  have p118_1 := h118c.2.1
                                  have p118_2 := h118c.2.2.1
                                  have p118_3 := h118c.2.2.2
                                  linarith only [hlam, p118_0]
                              · linarith only [h117, h56, h60, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                            · linarith only [h112, h116, h56, h61, hc35, hlam, hphi, u3ehi0]
                          · linarith only [h112, h115, h61, hlam]
                        · linarith only [h114, h60, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h112, h113, h56, hc35, hlam, hphi, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                      · linarith only [h112, h153, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                          · linarith only [h112, h156, h36, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h156, h61, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h155, h60, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                          · linarith only [h160, h164, h56, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h0, h161, h164, h48, hc01, hc13, hlam, hphi]
                        · linarith only [h161, h163, h56, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h161, h162, h56, hc35, hlam, hphi, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                      · linarith only [h161, h169, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h161, h171, h56, h60, hc34, hlam, hphi, u3ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                          · linarith only [h160, h161, h171, h173, hc45, hlam, hphi, ht34, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h160, h169, h175, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                              · linarith only [h0, h160, h161, h171, h177, h48, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h177, h56, hc45, hlam, hphi, ht34, u3ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                              · linarith only [h185, h56, h60, hc34, hlam, hphi, u3ehi0]
                              · linarith only [h160, h180, h182, h185, h56, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h160, h181, h184, hlam]
                          · linarith only [h160, h181, h183, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h180, h182, h56, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h180, h181, h56, hc35, hlam, hphi, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                      · linarith only [h180, h192, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                        · linarith only [h180, h194, h56, h60, hc34, hlam, hphi, u3ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                          · linarith only [h0, h160, h180, h196, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h160, h196, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT3_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
        · linarith only [h0, h2, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
        · linarith only [h2, h6, hc03, hlam, hphi, u3elo2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h1, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
          · linarith only [h8, hc24, hlam, hphi, ht45, u5elo4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h11 | h11
      · linarith only [h0, h1, h11, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
        · linarith only [h11, h13, hc03, hlam, hphi, u3elo2]
        · linarith only [h0, h1, h13, hc23, hlam, hphi, u3elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h16 | h16
    · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
          · linarith only [h16, h19, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
          · linarith only [h19, hc24, hlam, hphi, ht45, u5elo4]
        · linarith only [h0, h18, hc02, hlam, hphi, ht23, u3elo3]
      · linarith only [h0, h16, h17, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
      · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
        · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
            · linarith only [h24, h27, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
            · linarith only [h27, hc34, hlam, hphi, ht45, u5elo4]
          · linarith only [h16, h26, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h24, h25, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
        · linarith only [h24, h32, hc03, hlam, hphi, u3elo2]
        · linarith only [h0, h32, hc02, hlam, hphi, ht23, u3elo3]

theorem n7l_sBT3_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h5, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h11, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h10, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h17, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h19, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h19, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h16, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h23 | h23
            · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
              · linarith only [h0, h24, h3, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                · linarith only [h0, h26, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h26, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h23, h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
      · rcases m.htr 0 2 3 (by decide) (by decide) with h32 | h32
        · linarith only [h0, h1, h32, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
          · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
            · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h32, h36, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                · linarith only [h0, h1, h38, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h38, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1, h35, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
              · linarith only [h0, h1, h34, h43, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                · linarith only [h0, h1, h34, h45, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h45, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1, h42, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
    · rcases m.htr 0 1 5 (by decide) (by decide) with h51 | h51
      · rcases m.htr 0 2 3 (by decide) (by decide) with h52 | h52
        · rcases m.htr 0 3 4 (by decide) (by decide) with h53 | h53
          · rcases m.htr 0 3 5 (by decide) (by decide) with h54 | h54
            · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
              · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                  · linarith only [h0, h50, h57, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h50, h53, h57, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h56, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h50, h52, h53, h55, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h53, h54, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
              · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                  · linarith only [h50, h53, h66, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h0, h50, h68, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h63, h68, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h65, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h50, h52, h64, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h63, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h0, h50, h52, hlam]
      · linarith only [h51, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h76 | h76
      · rcases m.htr 0 2 3 (by decide) (by decide) with h77 | h77
        · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
          · rcases m.htr 0 3 5 (by decide) (by decide) with h79 | h79
            · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
              · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h77, h84, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h78, h84, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h50, h76, h81, h83, hc25, hlam, hphi, u5elo3]
                  · linarith only [h50, h76, h77, h78, h81, h82, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h50, h80, h81, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h77, h80, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h79, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                      · linarith only [h50, h76, h77, h78, h94, h97, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                        · linarith only [h77, h99, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h99, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h78, h92, h95, h96, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                      · linarith only [h104, h50, h76, h94, h95, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                        · linarith only [h106, h77, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h106, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h103, h50, h76, h92, h94, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h50, h76, h93, h94, hc15, hlam, hphi, u5elo2]
              · linarith only [h0, h76, h77, h93, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
            · linarith only [h92, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h113 | h113
          · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
            · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h113, h121, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h121, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h120, h77, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h113, h119, h77, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h115, h116, h118, h76, h77, hc25, hlam, hphi, u5elo3]
                  · linarith only [h0, h113, h115, h116, h117, h76, h77, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h0, h115, h116, h77, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                          · linarith only [h113, h134, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h134, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h115, h129, h133, h76, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h115, h129, h132, h76, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h131, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h113, h115, h129, h130, h76, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h0, h129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h114, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h143 | h143
            · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
              · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                      · linarith only [h0, h113, h144, h145, h148, h76, h77, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h145, h146, h148, h76, h77, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h147, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                      · linarith only [h144, h146, h153, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                          · rcases h3bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h50, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h77, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h113, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h156, hc45, hlam, hphi, ht0b, ht5b, p157_1, u0elo2]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h146, hc03, hc34, hlam, hphi, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h145, h146, h155, h156, h76, h77, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h146, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              rcases p157_3 (m.d 0 3) (by simp) with h167 | h167
                              · linarith only [h167, h50, hlam]
                              · linarith only [h143, h167, hlam]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h144, h145, h155, h156, h76, h77, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h144, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h153, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              rcases p157_3 (m.d 0 3) (by simp) with h174 | h174
                              · linarith only [h174, h77, hlam]
                              · linarith only [h143, h174, hlam]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              rcases p157_3 (m.d 0 3) (by simp) with h177 | h177
                              · linarith only [h177, hlam, p157_0]
                              · rcases p157_3 (m.d 1 3) (by simp) with h179 | h179
                                · linarith only [h146, h179, hlam]
                                · linarith only [h179, h50, hlam]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h145, h155, h156, h50, h76, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h145, h155, h156, h76, h77, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h0, h144, h145, h146, h155, h76, h77, hlam, p157_2]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h143, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h152, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h155, hlam, p157_0]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [h156, hlam, p157_1]
                            · have p157_0 := h157c.1
                              have p157_1 := h157c.2.1
                              have p157_2 := h157c.2.2.1
                              have p157_3 := h157c.2.2.2
                              linarith only [hlam, p157_0]
                          · linarith only [h0, h144, h146, h156, h77, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h145, h155, h76, h77, hc25, hlam, hphi, u5elo3]
                    · linarith only [h0, h143, h144, h145, h152, h76, h77, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h145, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                          · rcases h3bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h50, hlam, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h77, hlam, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h113, hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h113, h144, h196, h200, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              rcases p201_3 (m.d 0 3) (by simp) with h207 | h207
                              · linarith only [h207, h50, hlam]
                              · rcases p201_3 (m.d 1 3) (by simp) with h209 | h209
                                · rcases p201_3 (m.d 2 3) (by simp) with h210 | h210
                                  · rcases p201_3 (m.d 3 4) (by simp) with h211 | h211
                                    · linarith only [h196, h211, hlam]
                                    · linarith only [h113, h211, hlam]
                                  · linarith only [h210, h77, hlam]
                                · linarith only [h209, h50, hlam]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h144, hlam, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h113, h144, h195, h199, h200, h50, h76, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h0, h113, h195, h196, h199, h76, h77, hlam, p201_2]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              rcases p201_3 (m.d 0 3) (by simp) with h220 | h220
                              · linarith only [h220, h77, hlam]
                              · rcases p201_3 (m.d 1 3) (by simp) with h222 | h222
                                · linarith only [h144, h222, hlam]
                                · linarith only [h222, h50, hlam]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h0, h113, h195, h196, h199, h200, h76, h77, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h0, h113, h195, h199, h200, h76, h77, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h0, h144, h195, h199, h76, hlam, p201_2]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h0, h195, h196, h199, h200, h76, h77, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h196, hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h198, hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              rcases p201_3 (m.d 0 3) (by simp) with h233 | h233
                              · linarith only [h113, h233, hlam]
                              · linarith only [h143, h233, hlam]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h143, hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h197, hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h199, hlam, p201_0]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [h200, hlam, p201_1]
                            · have p201_0 := h201c.1
                              have p201_1 := h201c.2.1
                              have p201_2 := h201c.2.2.1
                              have p201_3 := h201c.2.2.2
                              linarith only [hlam, p201_0]
                          · linarith only [h200, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h144, h199, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h144, h196, h198, hlam]
                    · linarith only [h0, h113, h196, h197, h77, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                      · linarith only [h195, h196, h246, h50, h76, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h144, h195, h246, h76, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h144, h195, h245, h76, hc25, hlam, hphi, u5elo3]
                · linarith only [h0, h195, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h143, h76, h77, hc15, hlam, hphi, u5elo3]
      · linarith only [h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT3_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [hlam, hphi, ht34, ht45, u3ehi4, u5elo3]

theorem n7l_sBT3_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht0b, ht5b, u0elo4, u5ehi0]

theorem n7l_sBT3_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht0b, ht5b, u0elo4, u5ehi0]

theorem n7l_sBT3_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht0b, ht5b, u0elo4, u5ehi0]

theorem n7l_sBT3_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
        · linarith only [h0, h1, h3, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h1, h5, hc13, hlam, hphi, u3elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h8 | h8
    · linarith only [h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
      · linarith only [h10, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h10, h12, hc01, hlam, hphi, ht12, ht23, u3elo1]
        · linarith only [h0, h12, hc01, hlam, hphi, ht12, ht23, u3elo4]

theorem n7l_sBT3_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h0, h2, h6, hc34, hlam, hphi, u3ehi0]
          · linarith only [h0, h4, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
        · linarith only [h0, h4, h5, hc45, hlam, hphi, ht34, u3ehi0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, h2, h4, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
          · linarith only [h10, h12, h4, hc34, hlam, hphi, u3ehi2]
          · linarith only [h0, h12, hc45, hlam, hphi, ht34, u3ehi0]

theorem n7l_sBT3_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
  · linarith only [h0, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem n7l_sBT3_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3elo := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
    · linarith only [h0, h1, hc34, hlam, hphi, ht45, u5elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h8, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
          · linarith only [h10, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, h6, hc03, hlam, hphi, u3elo3]
            · linarith only [h0, h12, hc03, hlam, hphi, ht34, ht45, u5elo4]

theorem n7l_sBT3_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · linarith only [h0, h1, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
        · linarith only [h7, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
        · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
          · linarith only [h12, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h12, h14, h16, h6, hc01, hc13, hlam, hphi]
                · linarith only [h0, h16, h6, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h15, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h10, h14, h20, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h20, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem n7l_sBT3_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
  · linarith only [h0, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem n7l_sBT3_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h3elo := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo0]

theorem n7l_sBT3_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5bigk := hb5.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h10, h12, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h10, h15, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h10, h9, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h19, h3, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h19, h22, h7, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                            · rcases h5bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h19, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h22, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1, u3ehi4]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                rcases p25_3 (m.d 0 5) (by simp) with h30 | h30
                                · rcases p25_3 (m.d 1 5) (by simp) with h31 | h31
                                  · linarith only [h2, h31, hlam]
                                  · linarith only [h21, h31, hlam]
                                · linarith only [h30, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h2, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h22, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h19, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h4, hlam, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h8, hlam, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h22, hlam, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h6, hlam, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h3, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h3, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h24, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p25_1, u0ehi4]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h21, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h21, h22, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25_1, u3ehi2]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h24, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                            · linarith only [h21, h24, h9, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h0, h56, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                            · linarith only [h0, h21, h3, h5, h58, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h58, h7, h9, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h4, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                          · linarith only [h0, h3, h62, h66, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h3, h6, h62, h66, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                          · linarith only [h0, h3, h62, h69, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h3, h6, h62, h69, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h3, h6, h63, h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h0, h3, h5, h63, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h62, h7, h73, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                            · rcases h5bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h3, h6, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi4]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h3, h6, h62, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi4]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                rcases p81_3 (m.d 0 5) (by simp) with h86 | h86
                                · rcases p81_3 (m.d 1 5) (by simp) with h87 | h87
                                  · linarith only [h2, h87, hlam]
                                  · linarith only [h78, h87, hlam]
                                · linarith only [h86, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h2, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h62, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p81_1, u3ehi4]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h1, h76, h78, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h4, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h3, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi4]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h3, h79, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h6, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h77, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h79, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h2, h77, hc01, hc45, hlam, hphi, ht0b, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p81_1, u0ehi4]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h78, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, h3, h7, h76, h80, hc01, hc25, hlam, hphi, ht0b, ht5b, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h80, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                            · linarith only [h0, h3, h7, h76, h78, h80, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h3, h6, h7, h76, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                            · linarith only [h0, h114, h3, h7, h76, h78, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h5bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h3, h6, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u3ehi4]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h3, h6, h62, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u3ehi4]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h3, h6, h76, h78, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u3ehi3]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h2, hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h62, hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h114, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p116_1, u3ehi3]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h78, hlam, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h4, hlam, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h113, h114, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u3ehi3]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h0, h113, h3, h76, h78, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p116_1, u3ehi3]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h6, hlam, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h77, hlam, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h113, hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [hlam, p116_0]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h114, hlam, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p116_1, u0ehi4]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h62, hc12, hc45, hlam, hphi, ht23, ht34, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h62, hc12, hc45, hlam, hphi, ht23, ht34, p116_1]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [h114, hc45, hlam, hphi, ht34, p116_1, u3ehi3]
                              · have p116_0 := h116c.1
                                have p116_1 := h116c.2.1
                                have p116_2 := h116c.2.2.1
                                have p116_3 := h116c.2.2.2
                                linarith only [hlam, p116_0]
                          · linarith only [h113, h7, h77, hlam]
                      · linarith only [h76, h77, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                      · linarith only [h0, h144, h3, h5, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                          · linarith only [h0, h144, h147, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
                            · rcases h5bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h144, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h144, h4, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h147, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                rcases p150_3 (m.d 0 5) (by simp) with h155 | h155
                                · rcases p150_3 (m.d 1 5) (by simp) with h156 | h156
                                  · linarith only [h156, h2, hlam]
                                  · linarith only [h146, h156, hlam]
                                · linarith only [h155, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h2, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h62, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h144, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h4, hlam, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h147, hlam, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h6, hlam, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h144, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h3, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h0, h149, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p150_1, u0ehi4]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h146, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h146, h62, hlam, p150_1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h149, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                            · linarith only [h149, h76, hc45, hlam, hphi, ht34, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                          · linarith only [h0, h144, h181, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                            · linarith only [h146, h183, h76, hc34, hlam, hphi, u3ehi1]
                            · linarith only [h183, h76, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc15, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT3_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h3elo := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo0]

theorem n7l_sBT3_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h11, h6, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h10, h13, h2, h4, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases h3bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 3) (by simp) with h17 | h17
                            · rcases p15_3 (m.d 1 3) (by simp) with h18 | h18
                              · linarith only [h1, h18, hlam]
                              · rcases p15_3 (m.d 2 3) (by simp) with h20 | h20
                                · linarith only [h2, h20, hlam]
                                · rcases p15_3 (m.d 3 4) (by simp) with h22 | h22
                                  · linarith only [h22, h3, hlam]
                                  · rcases p15_3 (m.d 3 5) (by simp) with h24 | h24
                                    · linarith only [h24, h4, hlam]
                                    · linarith only [h24, h8, hlam]
                            · linarith only [h1, h17, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 3) (by simp) with h28 | h28
                            · rcases p15_3 (m.d 1 3) (by simp) with h29 | h29
                              · linarith only [h1, h29, hlam]
                              · linarith only [h29, h6, hlam]
                            · linarith only [h2, h28, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h10, h13, h3, h5, h6, h8, hlam, p15_2]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht5b, p15_1, u5ehi1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h1, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h10, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h8, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h2, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h6, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h11, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h3, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h7, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h10, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h13, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h4, hlam, p15_0]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h2, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [h0, h10, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            rcases p15_3 (m.d 0 3) (by simp) with h53 | h53
                            · rcases p15_3 (m.d 1 3) (by simp) with h54 | h54
                              · linarith only [h54, h8, hlam]
                              · linarith only [h54, h7, hlam]
                            · linarith only [h3, h53, hlam]
                          · have p15_0 := h15c.1
                            have p15_1 := h15c.2.1
                            have p15_2 := h15c.2.2.1
                            have p15_3 := h15c.2.2.2
                            linarith only [hlam, p15_0]
                    · linarith only [h10, h7, h8, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h0, h2, h3, h60, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                    · linarith only [h0, h6, h62, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                      · linarith only [h6, h60, h64, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                        · linarith only [h0, h2, h3, h66, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases h3bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h3, h5, h66, h7, hlam, p68_2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h3, h5, h6, h66, h7, hlam, p68_2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 3) (by simp) with h72 | h72
                            · rcases p68_3 (m.d 1 3) (by simp) with h73 | h73
                              · linarith only [h1, h73, hlam]
                              · rcases p68_3 (m.d 2 3) (by simp) with h75 | h75
                                · linarith only [h2, h75, hlam]
                                · rcases p68_3 (m.d 3 4) (by simp) with h77 | h77
                                  · linarith only [h77, hlam, p68_0]
                                  · rcases p68_3 (m.d 3 5) (by simp) with h79 | h79
                                    · linarith only [h4, h79, hlam]
                                    · linarith only [h66, h79, hlam]
                            · linarith only [h72, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h64, hc01, hlam, hphi, ht0b, ht5b, p68_1, u5ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h3, h5, h66, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h7, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h60, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h6, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h62, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h64, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h3, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h3, h5, h66, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h3, h5, h66, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h66, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h4, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 3) (by simp) with h100 | h100
                            · rcases p68_3 (m.d 1 3) (by simp) with h101 | h101
                              · linarith only [h101, hlam, p68_0]
                              · rcases p68_3 (m.d 2 3) (by simp) with h103 | h103
                                · linarith only [h103, h64, hlam]
                                · rcases p68_3 (m.d 3 4) (by simp) with h105 | h105
                                  · linarith only [h105, h66, hlam]
                                  · linarith only [h105, h7, hlam]
                            · linarith only [h1, h100, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 3) (by simp) with h109 | h109
                            · rcases p68_3 (m.d 1 3) (by simp) with h110 | h110
                              · linarith only [h110, h60, hlam]
                              · linarith only [h110, h6, hlam]
                            · linarith only [h109, h2, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h4, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h1, h117, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h0, h120, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                        · linarith only [h116, h122, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases h3bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            rcases p124_3 (m.d 0 3) (by simp) with h126 | h126
                            · rcases p124_3 (m.d 1 3) (by simp) with h127 | h127
                              · linarith only [h1, h127, hlam]
                              · rcases p124_3 (m.d 2 3) (by simp) with h129 | h129
                                · linarith only [h129, h2, hlam]
                                · linarith only [h129, h6, hlam]
                            · linarith only [h1, h126, hlam]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            rcases p124_3 (m.d 0 3) (by simp) with h133 | h133
                            · rcases p124_3 (m.d 1 3) (by simp) with h134 | h134
                              · linarith only [h1, h134, hlam]
                              · rcases p124_3 (m.d 2 3) (by simp) with h136 | h136
                                · linarith only [h136, h2, hlam]
                                · rcases p124_3 (m.d 3 4) (by simp) with h138 | h138
                                  · linarith only [h138, h3, hlam]
                                  · rcases p124_3 (m.d 3 5) (by simp) with h140 | h140
                                    · linarith only [h140, h4, hlam]
                                    · linarith only [h120, h140, hlam]
                            · linarith only [h133, h2, hlam]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h116, h120, h122, h3, h5, h6, hlam, p124_2]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, h120, h2, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h1, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h6, hlam, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, h120, h2, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h117, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h2, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h120, hc13, hc35, hlam, hphi, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, h120, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h120, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h3, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h116, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h119, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h122, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h4, hlam, p124_0]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, h116, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [h0, h2, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p124_1]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            rcases p124_3 (m.d 0 3) (by simp) with h164 | h164
                            · rcases p124_3 (m.d 1 3) (by simp) with h165 | h165
                              · linarith only [h117, h165, hlam]
                              · linarith only [h116, h165, hlam]
                            · linarith only [h164, h3, hlam]
                          · have p124_0 := h124c.1
                            have p124_1 := h124c.2.1
                            have p124_2 := h124c.2.2.1
                            have p124_3 := h124c.2.2.2
                            linarith only [hlam, p124_0]
                    · linarith only [h1, h116, h119, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h116, h171, h2, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                      · linarith only [h0, h171, h174, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                      · linarith only [h116, h173, h174, hc13, hc35, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                      · linarith only [h173, h177, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h0, h179, h2, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h173, h179, h6, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT3_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h1, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h10, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, h3, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h10, h14, h4, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h14, h4, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
            · linarith only [h1, h18, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h17, h18, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
            · linarith only [h17, h21, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h2, h23, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h23, h25, h26, h3, hc12, hc23, hlam, hphi]
                  · linarith only [h17, h26, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h17, h23, h29, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h25, h29, hc45, hlam, hphi, ht34, u3ehi2]
      · linarith only [h2, hc14, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT3_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h3elo := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo0]

theorem n7l_sBT3_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0ehi := hb0.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h12, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h15, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h10, h9, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h19, h2, h3, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                          · linarith only [h22, h6, h9, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h19, h24, h6, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h0, h26, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h21, h22, h26, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h29, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                            · linarith only [h0, h19, h2, h21, h3, h31, h5, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                              · linarith only [h0, h21, h33, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                                · linarith only [h21, h35, h6, h9, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h0, h2, h3, h35, h5, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h39, h6, h8, hlam]
                      · linarith only [h0, h2, h38, h39, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h38, h42, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h44, h7, h8, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h2, h3, h44, h46, h5, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                            · linarith only [h38, h48, h6, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h0, h2, h4, h48, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                    · linarith only [h52, h6, h7, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h2, h3, h52, h54, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                          · linarith only [h52, h57, h6, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h0, h2, h3, h57, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h2, h3, h5, h56, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                    · linarith only [h6, h61, h7, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                      · linarith only [h0, h2, h3, h61, h63, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                          · linarith only [h6, h61, h66, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h6, h66, h7, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h0, h2, h3, h5, h6, h65, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h2, h6, h71, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                        · linarith only [h0, h2, h6, h70, h75, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                          · linarith only [h0, h2, h6, h70, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h6, h74, h77, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h73, h74, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h6, h70, h73, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h2, h6, h82, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h0, h2, h6, h84, h90, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h0, h2, h70, h86, h87, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h70, h86, h89, hlam]
                            · linarith only [h6, h85, h88, hlam]
                          · linarith only [h6, h85, h87, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                              · linarith only [h0, h2, h84, h86, h96, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                                · linarith only [h100, h70, h84, h98, hlam]
                                · rcases h5bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    rcases p102_3 (m.d 0 5) (by simp) with h104 | h104
                                    · rcases p102_3 (m.d 1 5) (by simp) with h105 | h105
                                      · linarith only [h1, h105, hlam]
                                      · rcases p102_3 (m.d 2 5) (by simp) with h107 | h107
                                        · linarith only [h0, h107, h2, h84, h86, h97, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1, u3ehi3]
                                        · linarith only [h107, h82, hlam]
                                    · linarith only [h1, h104, hlam]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    rcases p102_3 (m.d 0 5) (by simp) with h111 | h111
                                    · rcases p102_3 (m.d 1 5) (by simp) with h112 | h112
                                      · linarith only [h1, h112, hlam]
                                      · rcases p102_3 (m.d 2 5) (by simp) with h114 | h114
                                        · linarith only [h114, hlam, p102_0]
                                        · rcases p102_3 (m.d 3 5) (by simp) with h116 | h116
                                          · linarith only [h116, h4, hlam]
                                          · rcases p102_3 (m.d 4 5) (by simp) with h118 | h118
                                            · linarith only [h118, h5, hlam]
                                            · linarith only [h118, h98, hlam]
                                    · linarith only [h111, hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    rcases p102_3 (m.d 0 5) (by simp) with h122 | h122
                                    · rcases p102_3 (m.d 1 5) (by simp) with h123 | h123
                                      · linarith only [h1, h123, hlam]
                                      · linarith only [h123, h85, hlam]
                                    · linarith only [h122, h4, hlam]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h3, h5, h70, h84, h98, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1, u3ehi3]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h1, hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h82, hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1, u3ehi4]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h86, hlam, p102_1]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h0, h2, h3, h5, h98, hc01, hlam, hphi, ht0b, ht5b, p102_1, u5ehi0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h0, h2, h3, h5, h98, hc01, hlam, hphi, ht0b, ht5b, p102_1, u5ehi1]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h0, h100, h2, h3, h5, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1, u3ehi3]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h98, hlam, p102_1]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h4, hlam, p102_1]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h85, hlam, p102_1]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h97, hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h100, hlam, p102_1]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h5, hlam, p102_0]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h0, h100, h2, h3, h5, h85, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1, u3ehi3]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h0, h2, h3, h5, hc01, hlam, hphi, ht0b, ht5b, p102_1, u5ehi2]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [h0, h100, h2, h3, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p102_1, u3ehi3]
                                  · have p102_0 := h102c.1
                                    have p102_1 := h102c.2.1
                                    have p102_2 := h102c.2.2.1
                                    have p102_3 := h102c.2.2.2
                                    linarith only [hlam, p102_0]
                            · linarith only [h6, h84, h97, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h6, h84, h96, hlam]
                      · linarith only [h84, h85, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                      · linarith only [h0, h151, h2, h3, h84, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                          · linarith only [h0, h154, h2, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                            · linarith only [h151, h154, h156, hc34, hlam, hphi, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
                                · rcases h5bigk with h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c | h160c
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 5) (by simp) with h162 | h162
                                    · rcases p160_3 (m.d 1 5) (by simp) with h163 | h163
                                      · linarith only [h1, h163, hlam]
                                      · rcases p160_3 (m.d 2 5) (by simp) with h165 | h165
                                        · linarith only [h0, h156, h159, h165, h2, h3, hc01, hlam, hphi, ht0b, ht5b, p160_1, u5ehi1]
                                        · linarith only [h165, h82, hlam]
                                    · linarith only [h1, h162, hlam]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 5) (by simp) with h169 | h169
                                    · rcases p160_3 (m.d 1 5) (by simp) with h170 | h170
                                      · linarith only [h1, h170, hlam]
                                      · rcases p160_3 (m.d 2 5) (by simp) with h172 | h172
                                        · linarith only [h172, hlam, p160_0]
                                        · rcases p160_3 (m.d 3 5) (by simp) with h174 | h174
                                          · linarith only [h174, h4, hlam]
                                          · linarith only [h156, h174, hlam]
                                    · linarith only [h169, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h151, h2, h3, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p160_1, u3ehi1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    rcases p160_3 (m.d 0 5) (by simp) with h179 | h179
                                    · rcases p160_3 (m.d 1 5) (by simp) with h180 | h180
                                      · linarith only [h1, h180, hlam]
                                      · linarith only [h153, h180, hlam]
                                    · linarith only [h179, h5, hlam]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h1, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h82, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h151, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p160_1, u5ehi4]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h158, hc24, hlam, hphi, ht01, ht12, p160_1, u0ehi4]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h156, h2, h4, hc01, hlam, hphi, ht0b, ht5b, p160_1, u5ehi1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h156, hlam, p160_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h154, h158, h2, h3, hc01, hlam, hphi, ht0b, ht5b, p160_1, u5ehi4]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h4, hlam, p160_1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h151, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p160_1, u3ehi1]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, p160_1, u5ehi2]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h0, h159, h2, h3, hc01, hlam, hphi, ht0b, ht5b, p160_1, u5ehi4]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h5, hlam, p160_0]
                                  · have p160_0 := h160c.1
                                    have p160_1 := h160c.2.1
                                    have p160_2 := h160c.2.2.1
                                    have p160_3 := h160c.2.2.2
                                    linarith only [h153, hlam, p160_0]
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
                                · linarith only [h153, h154, h159, h70, hlam]
                              · linarith only [h153, h158, h70, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                          · linarith only [h0, h2, h206, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                            · linarith only [h206, h208, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
                              · linarith only [h0, h153, h2, h206, h210, h3, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h212 | h212
                                · linarith only [h0, h2, h206, h210, h212, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h0, h2, h212, h3, h5, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h0, h1, hc15, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT3_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sBT3_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]

theorem n7l_sBT3_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h15, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
                              · linarith only [h14, h5, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                                · linarith only [h0, h20, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h20, h6, hc23, hlam, hphi, u3elo0]
                              · linarith only [h19, h5, hc23, hlam, hphi, u3elo0]
                          · linarith only [h12, h6, hc13, hlam, hphi, u3elo0]
                        · linarith only [h11, h5, h8, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                        · linarith only [h28, h8, h9, hlam]
                        · linarith only [h28, h5, hc13, hlam, hphi, u3elo0]
                      · linarith only [h27, h4, h5, h7, h8, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                      · linarith only [h33, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                            · linarith only [h32, h33, h37, h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                                  · linarith only [h32, h33, h37, h4, h41, h5, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                  · linarith only [h33, h41, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
                                · linarith only [h36, h40, hc23, hlam, hphi, u3elo1]
                              · linarith only [h39, h5, h8, hc13, hlam, hphi, u3elo0]
                          · linarith only [h36, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h32, h35, h5, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                      · linarith only [h48, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                                    · linarith only [h50, h56, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                                    · rcases h5bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0, u5ehi1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h48, h5, h7, hc12, hlam, hphi, ht23, p58_1, u3elo0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0, u5ehi3]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h5, h56, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p58_1, u3elo0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h2, hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h48, hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p58_1, u5ehi3]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h2, h56, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p58_1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h4, hlam, p58_1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0, u5ehi1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0, u5ehi3]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h4, h5, h56, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p58_1, u3elo0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h6, hlam, p58_1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h51, hlam, p58_1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h54, hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h56, hlam, p58_1]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h7, hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h52, hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h55, hlam, p58_0]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [h52, hc14, hlam, hphi, ht01, ht0b, ht5b, p58_1, u5ehi3]
                                      · have p58_0 := h58c.1
                                        have p58_1 := h58c.2.1
                                        have p58_2 := h58c.2.2.1
                                        have p58_3 := h58c.2.2.2
                                        linarith only [hlam, p58_0]
                                  · linarith only [h3, h32, h50, h52, h55, h8, hc12, hlam, hphi, ht23, u3elo0]
                                · linarith only [h50, h52, h54, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                              · linarith only [h50, h52, h53, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                            · linarith only [h32, h5, h52, h7, hc12, hlam, hphi, ht23, u3elo0]
                          · linarith only [h51, h6, hc13, hlam, hphi, u3elo0]
                        · linarith only [h5, h50, h8, hc12, hlam, hphi, ht23, u3elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                            · linarith only [h7, h93, h95, hc13, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                                · linarith only [h0, h90, h98, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h6, h98, hc23, hlam, hphi, u3elo0]
                              · linarith only [h5, h97, hc23, hlam, hphi, u3elo0]
                          · linarith only [h6, h94, hc13, hlam, hphi, u3elo0]
                        · linarith only [h5, h90, h93, hc23, hlam, hphi, u3elo0]
                      · linarith only [h4, h6, h90, h92, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                        · linarith only [h106, h90, h91, hlam]
                        · linarith only [h106, h5, hc13, hlam, hphi, u3elo0]
                      · linarith only [h105, h4, h6, h90, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h111, h90, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                            · linarith only [h110, h111, h115, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                                  · linarith only [h110, h111, h119, h4, h6, h7, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                                    · linarith only [h110, h111, h117, h121, h4, h6, h7, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo0]
                                    · rcases h5bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p123_1, u3elo0, u5ehi1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h111, h6, hc12, hlam, hphi, ht23, p123_1, u3elo0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p123_1, u3elo0, u5ehi3]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h7, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h2, hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h111, hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p123_1, u5ehi3]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h115, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h4, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p123_1, u5ehi1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p123_1, u3elo0, u5ehi3]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h119, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h6, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h114, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h118, hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [hlam, p123_0]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h121, hlam, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p123_1, u0ehi4]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h110, h111, h117, hc34, hc45, hlam, hphi, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [h110, h111, h117, hc34, hc45, hlam, hphi, p123_1]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        rcases p123_3 (m.d 0 5) (by simp) with h147 | h147
                                        · linarith only [h147, h7, hlam]
                                        · linarith only [h147, h6, hlam]
                                      · have p123_0 := h123c.1
                                        have p123_1 := h123c.2.1
                                        have p123_2 := h123c.2.2.1
                                        have p123_3 := h123c.2.2.2
                                        linarith only [hlam, p123_0]
                                · linarith only [h114, h118, hc23, hlam, hphi, u3elo1]
                              · linarith only [h114, h117, h90, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                          · linarith only [h114, h6, hc13, hlam, hphi, u3elo0]
                        · linarith only [h113, h5, h90, hc12, hlam, hphi, ht23, u3elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                      · linarith only [h155, h90, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                            · linarith only [h159, h7, hc14, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                                  · linarith only [h161, h163, h3, h7, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h165 | h165
                                    · linarith only [h110, h157, h163, h165, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases h5bigk with h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c | h167c
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p167_1, u3elo0, u5ehi1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p167_1, u3elo0, u5ehi2]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p167_1, u3elo0, u5ehi3]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h7, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h2, hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h155, hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p167_1, u5ehi3]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h159, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h4, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p167_1, u5ehi1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p167_1, u3elo0, u5ehi3]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h163, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h6, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h158, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h162, hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [hlam, p167_0]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h165, hlam, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p167_1, u0ehi4]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        rcases p167_3 (m.d 0 5) (by simp) with h189 | h189
                                        · linarith only [h189, h7, hlam]
                                        · linarith only [h189, h2, hlam]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [h155, hc12, hc45, hlam, hphi, ht23, ht34, p167_1]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        rcases p167_3 (m.d 0 5) (by simp) with h193 | h193
                                        · linarith only [h193, h7, hlam]
                                        · linarith only [h193, h6, hlam]
                                      · have p167_0 := h167c.1
                                        have p167_1 := h167c.2.1
                                        have p167_2 := h167c.2.2.1
                                        have p167_3 := h167c.2.2.2
                                        linarith only [hlam, p167_0]
                                · linarith only [h162, h6, h90, hc13, hlam, hphi, u3elo0]
                              · linarith only [h158, h161, h90, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                          · linarith only [h158, h6, hc13, hlam, hphi, u3elo0]
                        · linarith only [h157, h5, h90, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
            · rcases m.htr 0 3 5 (by decide) (by decide) with h204 | h204
              · linarith only [h204, h3, h4, hlam]
              · linarith only [h204, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h203, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h209 | h209
        · rcases m.htr 0 2 5 (by decide) (by decide) with h210 | h210
          · linarith only [h0, h2, h210, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h212 | h212
            · rcases m.htr 0 3 5 (by decide) (by decide) with h213 | h213
              · linarith only [h0, h2, h209, h213, hlam]
              · linarith only [h212, h213, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
            · linarith only [h212, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h209, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h219 | h219
    · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
      · rcases m.htr 0 2 3 (by decide) (by decide) with h221 | h221
        · rcases m.htr 0 2 5 (by decide) (by decide) with h222 | h222
          · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
            · rcases m.htr 0 3 5 (by decide) (by decide) with h224 | h224
              · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
                · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                          · linarith only [h0, h219, h230, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h224, h230, hc13, hlam, hphi, u3elo0]
                        · linarith only [h223, h226, h229, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h220, h228, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h220, h227, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h219, h223, h225, h226, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h0, h219, h241, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h224, h241, hc13, hlam, hphi, u3elo0]
                        · linarith only [h223, h237, h240, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h220, h239, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h220, h238, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h237, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h223, h224, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
            · linarith only [h223, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · linarith only [h0, h220, h222, hlam]
        · linarith only [h0, h221, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h252 | h252
        · rcases m.htr 0 2 5 (by decide) (by decide) with h253 | h253
          · rcases m.htr 0 3 4 (by decide) (by decide) with h254 | h254
            · rcases m.htr 0 3 5 (by decide) (by decide) with h255 | h255
              · linarith only [h219, h220, h255, hlam]
              · linarith only [h254, h255, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
            · linarith only [h254, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
            · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
              · linarith only [h0, h219, h253, h260, hlam]
              · linarith only [h259, h260, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
            · linarith only [h259, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h0, h219, h252, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
    · linarith only [h219, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem n7l_sBT3_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3ehi := hb3.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi2, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
                              · linarith only [h14, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h13, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h10, h12, h7, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h0, h10, h22, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h22, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                          · linarith only [h1, h31, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                                · linarith only [h0, h1, h29, h33, h35, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                                  · linarith only [h0, h29, h37, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h1, h33, h37, h7, hc23, hlam, hphi, u3elo3]
                              · linarith only [h34, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h33, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h30, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h29, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h28, h7, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h27, h4, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
              · rcases m.htr 0 3 4 (by decide) (by decide) with h48 | h48
                · linarith only [h4, h48, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                          · linarith only [h1, h48, h54, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                                · linarith only [h0, h48, h52, h58, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h0, h5, h52, h58, hc23, hlam, hphi, u3elo3]
                              · linarith only [h54, h56, h57, hc35, hlam, hphi, u5elo4]
                            · linarith only [h56, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h52, h53, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h4, h5, h52, hc12, hc24, hlam, hphi]
                    · linarith only [h5, h51, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h50, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h4, h47, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
            · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
              · rcases m.htr 0 3 4 (by decide) (by decide) with h70 | h70
                · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                      · linarith only [h0, h4, h73, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                                    · linarith only [h4, h68, h79, h81, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                    · linarith only [h81, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h4, h68, h77, h79, h80, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h4, h79, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h78, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h77, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h70, h73, h75, h76, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h75, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h72, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h71, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h4, h68, h70, hlam]
              · linarith only [h68, h69, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h94 | h94
              · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
                · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h4, h95, h98, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
                                    · linarith only [h1, h101, h106, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h106, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h104, h105, h68, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h0, h100, h104, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h103, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h102, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h100, h101, h95, h98, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h100, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h68, h97, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h68, h94, h95, h96, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
                      · linarith only [h0, h119, h4, h95, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                          · linarith only [h1, h122, h4, h95, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                                · linarith only [h0, h121, h126, h4, h95, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h0, h121, h126, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h122, h125, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h119, h121, h124, hc25, hlam, hphi, u5elo3]
                        · linarith only [h121, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h118, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h117, h4, h94, hc25, hlam, hphi, u5elo3]
              · linarith only [h94, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
        · rcases m.htr 0 2 3 (by decide) (by decide) with h137 | h137
          · rcases m.htr 0 2 4 (by decide) (by decide) with h138 | h138
            · linarith only [h0, h138, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h140 | h140
              · rcases m.htr 0 3 4 (by decide) (by decide) with h141 | h141
                · linarith only [h1, h141, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h143 | h143
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                      · linarith only [h0, h141, h145, h2, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h137, h141, h145, h2, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h144, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h143, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h137, h140, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h151 | h151
            · linarith only [h0, h137, h151, h2, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
              · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
                · linarith only [h1, h154, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                      · linarith only [h0, h137, h154, h158, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                          · linarith only [h0, h154, h160, h161, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1, h158, h160, h161, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h160, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h157, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h137, h153, h156, hc25, hlam, hphi, u5elo3]
              · linarith only [h153, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h136, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h170 | h170
    · rcases m.htr 0 1 4 (by decide) (by decide) with h171 | h171
      · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
        · rcases m.htr 0 2 3 (by decide) (by decide) with h173 | h173
          · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
            · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
              · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
                · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                                    · linarith only [h170, h179, h184, h186, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h186, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h185, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h176, h184, hc23, hlam, hphi, u3elo0]
                              · linarith only [h183, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h182, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h176, h179, h181, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h180, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h179, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h178, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h176, h177, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                          · linarith only [h170, h176, h202, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                                · linarith only [h176, h206, hc03, hlam, hphi, u3elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                                    · rcases h0bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h0, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h0, h170, h200, h208, h209, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p210_1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h0, h170, h176, h200, h208, h209, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p210_1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        rcases p210_3 (m.d 0 1) (by simp) with h215 | h215
                                        · rcases p210_3 (m.d 0 2) (by simp) with h216 | h216
                                          · rcases p210_3 (m.d 0 3) (by simp) with h217 | h217
                                            · linarith only [h170, h217, hlam]
                                            · linarith only [h198, h217, hlam]
                                          · linarith only [h175, h216, hlam]
                                        · linarith only [h172, h215, hlam]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h170, h200, h208, h209, hc45, hlam, hphi, ht0b, ht5b, p210_1, u0elo1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h170, h200, h208, h209, hc45, hlam, hphi, ht0b, ht5b, p210_1, u0elo1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h170, h176, h200, h208, h209, hc45, hlam, hphi, ht0b, ht5b, p210_1, u0elo1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        rcases p210_3 (m.d 0 1) (by simp) with h226 | h226
                                        · linarith only [h0, h226, hlam]
                                        · linarith only [h172, h226, hlam]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h170, hlam, p210_1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h173, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h176, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h172, h176, h201, h208, h209, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p210_1, u3elo3]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h171, hlam, p210_1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h174, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h170, h200, h208, h209, hc45, hlam, hphi, ht0b, ht5b, p210_1, u0elo3]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        rcases p210_3 (m.d 0 1) (by simp) with h238 | h238
                                        · rcases p210_3 (m.d 0 2) (by simp) with h239 | h239
                                          · rcases p210_3 (m.d 0 3) (by simp) with h240 | h240
                                            · linarith only [h176, h240, hlam]
                                            · linarith only [h198, h240, hlam]
                                          · linarith only [h175, h239, hlam]
                                        · linarith only [h172, h238, hlam]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h172, hlam, p210_1]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h175, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h198, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [h199, hlam, p210_0]
                                      · have p210_0 := h210c.1
                                        have p210_1 := h210c.2.1
                                        have p210_2 := h210c.2.2.1
                                        have p210_3 := h210c.2.2.2
                                        linarith only [hlam, p210_0]
                                    · linarith only [h176, h209, hc04, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h170, h176, h204, h208, hc23, hlam, hphi, u3elo3]
                              · linarith only [h205, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h204, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h201, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h200, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h176, h198, h199, hc35, hlam, hphi, u5elo4]
                  · linarith only [h198, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h175, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h171, h174, hlam]
          · linarith only [h0, h170, h173, hc13, hlam, hphi, u3elo2]
        · linarith only [h170, h172, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
              · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
                · linarith only [h170, h171, h266, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                          · linarith only [h170, h266, h272, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h170, h171, h272, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h170, h270, h271, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h270, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h269, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h263, h268, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h170, h171, h264, h265, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                · linarith only [h0, h170, h264, h281, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h283 | h283
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                          · linarith only [h170, h281, h287, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h170, h171, h287, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h170, h285, h286, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h285, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h264, h284, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h283, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h170, h280, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h170, h263, hc13, hlam, hphi, u3elo2]
        · linarith only [h170, h262, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h297 | h297
      · rcases m.htr 0 1 5 (by decide) (by decide) with h298 | h298
        · rcases m.htr 0 2 3 (by decide) (by decide) with h299 | h299
          · rcases m.htr 0 2 4 (by decide) (by decide) with h300 | h300
            · rcases m.htr 0 2 5 (by decide) (by decide) with h301 | h301
              · rcases m.htr 0 3 4 (by decide) (by decide) with h302 | h302
                · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                              · linarith only [h170, h297, h309, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h307, h309, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h170, h297, h307, h308, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h170, h307, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h306, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h297, h299, h305, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h304, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h303, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h170, h297, h302, hlam]
              · linarith only [h301, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h170, h297, h299, h300, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h321 | h321
            · rcases m.htr 0 2 5 (by decide) (by decide) with h322 | h322
              · rcases m.htr 0 3 4 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 3 5 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h329 | h329
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                              · linarith only [h0, h297, h299, h326, h330, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h328, h330, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h299, h326, h329, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h299, h326, h328, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h327, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h297, h325, h326, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h325, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h324, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h297, h299, h323, hlam]
              · linarith only [h0, h297, h322, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h297, h321, hlam]
        · linarith only [h297, h298, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h343 | h343
        · rcases m.htr 0 2 3 (by decide) (by decide) with h344 | h344
          · rcases m.htr 0 2 4 (by decide) (by decide) with h345 | h345
            · rcases m.htr 0 2 5 (by decide) (by decide) with h346 | h346
              · rcases m.htr 0 3 4 (by decide) (by decide) with h347 | h347
                · rcases m.htr 0 3 5 (by decide) (by decide) with h348 | h348
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h349 | h349
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h356 | h356
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h357 | h357
                                    · linarith only [h344, h355, h357, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h357, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h356, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h170, h347, h355, hc23, hlam, hphi, u3elo1]
                              · linarith only [h297, h343, h351, h354, hc25, hlam, hphi, u5elo4]
                            · linarith only [h297, h343, h351, h352, h353, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h170, h347, h352, hlam]
                        · linarith only [h0, h351, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h350, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h297, h343, h349, hc15, hlam, hphi, u5elo4]
                  · linarith only [h297, h343, h347, h348, hc15, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                          · linarith only [h347, h373, hc03, hlam, hphi, u3elo1]
                          · linarith only [h170, h343, h372, h373, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h170, h371, h372, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h343, h371, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h170, h343, h347, h370, hc15, hlam, hphi, u5elo4]
                  · linarith only [h170, h343, h369, hc15, hlam, hphi, u5elo3]
              · linarith only [h344, h346, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h381 | h381
              · rcases m.htr 0 3 4 (by decide) (by decide) with h382 | h382
                · linarith only [h344, h345, h382, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                          · linarith only [h170, h343, h382, h387, h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h170, h343, h387, h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h387, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h343, h386, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h345, h385, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h170, h343, h384, hc15, hlam, hphi, u5elo3]
              · linarith only [h344, h381, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h396 | h396
            · rcases m.htr 0 2 5 (by decide) (by decide) with h397 | h397
              · rcases m.htr 0 3 4 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 3 5 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h407 | h407
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                                    · linarith only [h344, h396, h401, h406, h408, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · linarith only [h408, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h297, h344, h396, h407, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h297, h344, h396, h406, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · linarith only [h297, h343, h402, h405, hc25, hlam, hphi, u5elo4]
                            · linarith only [h297, h343, h344, h396, h401, h402, h404, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h297, h343, h344, h396, h398, h401, h402, h403, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h297, h343, h344, h396, h401, h402, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h343, h401, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h297, h343, h400, hc15, hlam, hphi, u5elo4]
                  · linarith only [h399, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h344, h396, h398, hlam]
              · linarith only [h297, h343, h396, h397, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h422 | h422
              · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
                · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h428 | h428
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h430 | h430
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h431 | h431
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                                    · rcases h0bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h0, hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h170, hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h297, hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h170, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p434_1, u3elo1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h396, hc01, hc24, hlam, hphi, ht12, p434_1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h344, hlam, p434_1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h396, hlam, p434_1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h343, h344, h426, h427, h432, h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p434_1, u3elo1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h343, h344, h426, h427, h432, h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p434_1, u3elo1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h344, h426, hc02, hlam, hphi, ht23, p434_1, u3elo1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h0, h343, h344, h396, h426, h427, h432, h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p434_1, u3elo1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        rcases p434_3 (m.d 0 1) (by simp) with h449 | h449
                                        · linarith only [h170, h449, hlam]
                                        · linarith only [h343, h449, hlam]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h343, h427, h432, h433, hc45, hlam, hphi, ht0b, ht5b, p434_1, u0elo3]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h0, h343, h396, h426, h427, h431, h432, h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p434_1, u3elo1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h423, hlam, p434_1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        rcases p434_3 (m.d 0 1) (by simp) with h456 | h456
                                        · linarith only [h297, h456, hlam]
                                        · linarith only [h343, h456, hlam]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h343, hlam, p434_1]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h422, hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h424, hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [h425, hlam, p434_0]
                                      · have p434_0 := h434c.1
                                        have p434_1 := h434c.2.1
                                        have p434_2 := h434c.2.2.1
                                        have p434_3 := h434c.2.2.2
                                        linarith only [hlam, p434_0]
                                    · linarith only [h433, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h396, h431, h432, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h343, h344, h427, h431, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h297, h430, hc04, hlam, hphi, ht45, u5elo4]
                            · linarith only [h429, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h344, h423, h426, h428, hlam]
                        · linarith only [h0, h343, h344, h426, h427, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h343, h426, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h425, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h424, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h477 | h477
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
                          · linarith only [h0, h343, h344, h423, h477, h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h170, h343, h477, h478, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h343, h344, h476, h477, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h343, h476, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h0, h343, h344, h423, h475, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h343, h344, h474, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h343, h422, hc15, hlam, hphi, u5elo2]
        · linarith only [h343, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sBT3_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [hlam, hphi, ht34, ht45, u3ehi4, u5elo3]

theorem n7l_sBT3_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
            · linarith only [h4, h5, h7, hlam]
            · linarith only [h1, h2, h7, hc23, hlam, hphi, u3elo4]
        · linarith only [h1, h2, h4, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h11 | h11
      · linarith only [h1, h11, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
        · linarith only [h0, h1, h13, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h15, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
            · linarith only [h15, h17, hc13, hlam, hphi, u3elo2]
            · linarith only [h1, h17, hc02, hlam, hphi, ht23, u3elo4]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 2 5 (by decide) (by decide) with h21 | h21
      · linarith only [h21, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
        · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
          · linarith only [h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
          · linarith only [h0, h24, hc01, hlam, hphi, ht12, ht23, u3elo4]
        · linarith only [h20, h21, h23, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
      · linarith only [h28, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
          · linarith only [h31, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
          · linarith only [h20, h30, h31, hc02, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
          · linarith only [h34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
          · linarith only [h0, h34, hc01, hlam, hphi, ht12, ht23, u3elo4]

theorem n7l_sBT3_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · linarith only [h0, h1, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h10, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
            · linarith only [h0, h10, hc45, hlam, hphi, ht34, u3ehi0]
          · linarith only [h0, h8, h9, hc45, hlam, hphi, ht34, u3ehi0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h0, h14, h6, h8, hc34, hlam, hphi, u3ehi0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
            · linarith only [h0, h16, h6, hc34, hlam, hphi, u3ehi0]
            · linarith only [h0, h16, hc45, hlam, hphi, ht34, u3ehi0]

theorem n7l_sBT3_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3ehi := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht34, ht45, p0_1, u3ehi4, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · linarith only [h5, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
            · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h8, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
            · linarith only [h11, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h11, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h15 | h15
    · rcases p0_3 (m.d 0 2) (by simp) with h16 | h16
      · rcases p0_3 (m.d 0 3) (by simp) with h17 | h17
        · linarith only [h17, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 0 5) (by simp) with h20 | h20
            · linarith only [h20, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h20, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
            · linarith only [h23, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h23, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h16, h29, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
            · linarith only [h32, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h32, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · rcases p0_3 (m.d 0 2) (by simp) with h37 | h37
      · rcases p0_3 (m.d 0 3) (by simp) with h38 | h38
        · rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
          · linarith only [h39, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h41 | h41
            · linarith only [h41, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h41, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h44 | h44
          · linarith only [h44, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
            · linarith only [h38, h46, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h46, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h49 | h49
        · linarith only [h37, h49, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h51 | h51
          · linarith only [h51, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · linarith only [h37, h53, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h53, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h58 | h58
    · linarith only [h58, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h60 | h60
      · rcases p0_3 (m.d 0 3) (by simp) with h61 | h61
        · linarith only [h61, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h63 | h63
          · rcases p0_3 (m.d 0 5) (by simp) with h64 | h64
            · linarith only [h64, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h64, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h67 | h67
            · linarith only [h67, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h67, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h60, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h72 | h72
    · rcases p0_3 (m.d 0 2) (by simp) with h73 | h73
      · rcases p0_3 (m.d 0 3) (by simp) with h74 | h74
        · linarith only [h74, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
          · rcases p0_3 (m.d 0 5) (by simp) with h77 | h77
            · linarith only [h77, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h72, h77, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h80 | h80
            · linarith only [h80, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h80, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h73, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h84 | h84
      · rcases p0_3 (m.d 0 3) (by simp) with h85 | h85
        · linarith only [h85, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h87 | h87
          · rcases p0_3 (m.d 0 5) (by simp) with h88 | h88
            · linarith only [h72, h88, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h88, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h91 | h91
            · linarith only [h91, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h91, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h84, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h95 | h95
    · rcases p0_3 (m.d 0 2) (by simp) with h96 | h96
      · rcases p0_3 (m.d 0 3) (by simp) with h97 | h97
        · rcases p0_3 (m.d 0 4) (by simp) with h98 | h98
          · linarith only [h98, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h100 | h100
            · linarith only [h100, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h100, h95, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · linarith only [h103, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h105 | h105
            · linarith only [h105, h97, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h105, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h96, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h109 | h109
      · rcases p0_3 (m.d 0 3) (by simp) with h110 | h110
        · linarith only [h110, h95, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
          · linarith only [h112, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h114 | h114
            · linarith only [h114, h95, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h114, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h109, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h122 | h122
    · rcases p0_3 (m.d 0 2) (by simp) with h123 | h123
      · rcases p0_3 (m.d 0 3) (by simp) with h124 | h124
        · rcases p0_3 (m.d 0 4) (by simp) with h125 | h125
          · linarith only [h125, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h127 | h127
            · linarith only [h127, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h122, h127, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · linarith only [h124, hlam, p0_0]
      · linarith only [h123, hc02, hlam, hphi, ht23, p0_1, u3elo0]
    · linarith only [h122, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h134 | h134
    · linarith only [h134, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h136 | h136
      · rcases p0_3 (m.d 0 3) (by simp) with h137 | h137
        · linarith only [h137, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
          · rcases p0_3 (m.d 0 5) (by simp) with h140 | h140
            · linarith only [h140, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h136, h140, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h139, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h144 | h144
        · linarith only [h144, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h147, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h146, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h151 | h151
    · rcases p0_3 (m.d 0 2) (by simp) with h152 | h152
      · linarith only [h152, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h154 | h154
        · linarith only [h154, hc02, hlam, hphi, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 0 5) (by simp) with h157 | h157
            · linarith only [h157, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h151, h157, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h156, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h163 | h163
        · linarith only [h151, h163, hc01, hlam, hphi, ht12, ht23, p0_1, u3elo0]
        · rcases p0_3 (m.d 0 4) (by simp) with h165 | h165
          · rcases p0_3 (m.d 0 5) (by simp) with h166 | h166
            · linarith only [h151, h166, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h166, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h165, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h170 | h170
    · rcases p0_3 (m.d 0 2) (by simp) with h171 | h171
      · rcases p0_3 (m.d 0 3) (by simp) with h172 | h172
        · linarith only [h172, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h174 | h174
          · rcases p0_3 (m.d 0 5) (by simp) with h175 | h175
            · linarith only [h175, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h170, h175, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h174, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h179 | h179
        · linarith only [h179, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h181 | h181
          · rcases p0_3 (m.d 0 5) (by simp) with h182 | h182
            · linarith only [h171, h182, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h182, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h181, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h186 | h186
      · rcases p0_3 (m.d 0 3) (by simp) with h187 | h187
        · linarith only [h187, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h189 | h189
          · rcases p0_3 (m.d 0 5) (by simp) with h190 | h190
            · linarith only [h170, h190, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h186, h190, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h189, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h194 | h194
        · linarith only [h194, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h196 | h196
          · rcases p0_3 (m.d 0 5) (by simp) with h197 | h197
            · linarith only [h170, h197, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h197, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h196, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · linarith only [h7, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h7, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h10 | h10
            · linarith only [h10, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h10, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · linarith only [h14, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h14, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h17 | h17
            · linarith only [h17, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h17, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · rcases p0_3 (m.d 0 2) (by simp) with h22 | h22
      · rcases p0_3 (m.d 0 3) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
            · linarith only [h26, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h26, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · linarith only [h29, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 0 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h38, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h42 | h42
    · rcases p0_3 (m.d 0 2) (by simp) with h43 | h43
      · rcases p0_3 (m.d 0 3) (by simp) with h44 | h44
        · rcases p0_3 (m.d 0 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · linarith only [h47, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h47, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h52, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
      · rcases p0_3 (m.d 0 3) (by simp) with h55 | h55
        · rcases p0_3 (m.d 0 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h58, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h63, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h70 | h70
      · rcases p0_3 (m.d 0 3) (by simp) with h71 | h71
        · rcases p0_3 (m.d 0 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 0 5) (by simp) with h73 | h73
            · linarith only [h73, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h73, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h76 | h76
            · linarith only [h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h76, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 0 5) (by simp) with h80 | h80
            · linarith only [h80, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h80, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h83 | h83
            · linarith only [h83, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h83, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h88 | h88
    · rcases p0_3 (m.d 0 2) (by simp) with h89 | h89
      · rcases p0_3 (m.d 0 3) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 0 5) (by simp) with h93 | h93
            · linarith only [h93, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h88, h93, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h96 | h96
            · linarith only [h96, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h96, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h100 | h100
      · rcases p0_3 (m.d 0 3) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h104, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · linarith only [h107, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h107, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h111 | h111
    · rcases p0_3 (m.d 0 2) (by simp) with h112 | h112
      · rcases p0_3 (m.d 0 3) (by simp) with h113 | h113
        · rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h116 | h116
            · linarith only [h116, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h111, h116, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h121, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h125 | h125
      · rcases p0_3 (m.d 0 3) (by simp) with h126 | h126
        · rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h129, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h134, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h141 | h141
      · rcases p0_3 (m.d 0 3) (by simp) with h142 | h142
        · rcases p0_3 (m.d 0 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 0 5) (by simp) with h144 | h144
            · linarith only [h144, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h144, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h147, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h151 | h151
        · rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · linarith only [h153, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h153, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h156 | h156
            · linarith only [h156, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h156, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h163 | h163
        · rcases p0_3 (m.d 0 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
            · linarith only [h165, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h160, h165, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
            · linarith only [h168, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h160, h168, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h174 | h174
        · rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h176, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h179 | h179
            · linarith only [h179, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h179, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h184 | h184
    · rcases p0_3 (m.d 0 2) (by simp) with h185 | h185
      · rcases p0_3 (m.d 0 3) (by simp) with h186 | h186
        · rcases p0_3 (m.d 0 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h189 | h189
            · linarith only [h189, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h184, h189, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h193 | h193
        · rcases p0_3 (m.d 0 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h196, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h200 | h200
      · rcases p0_3 (m.d 0 3) (by simp) with h201 | h201
        · rcases p0_3 (m.d 0 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h200, h204, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h208 | h208
        · rcases p0_3 (m.d 0 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h211, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h218 | h218
      · rcases p0_3 (m.d 0 3) (by simp) with h219 | h219
        · rcases p0_3 (m.d 0 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 0 5) (by simp) with h221 | h221
            · linarith only [h221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h218, h221, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 0 5) (by simp) with h226 | h226
            · linarith only [h226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h226, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h230 | h230
        · rcases p0_3 (m.d 0 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · linarith only [h232, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h230, h232, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 0 5) (by simp) with h237 | h237
            · linarith only [h237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h237, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h241 | h241
    · rcases p0_3 (m.d 0 2) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h244 | h244
        · rcases p0_3 (m.d 0 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 0 5) (by simp) with h246 | h246
            · linarith only [h246, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h241, h246, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 0 5) (by simp) with h251 | h251
            · linarith only [h251, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h251, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h257 | h257
        · rcases p0_3 (m.d 0 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 0 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h257, h259, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h264, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h268 | h268
    · rcases p0_3 (m.d 0 2) (by simp) with h269 | h269
      · rcases p0_3 (m.d 0 3) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 0 5) (by simp) with h273 | h273
            · linarith only [h273, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h268, h273, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 0 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h280, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h284 | h284
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 0 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h284, h288, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 0 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h295, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht45, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
          · linarith only [h4, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
        · linarith only [h1, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
      · linarith only [h0, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
    · linarith only [h1, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc34, hlam, hphi, u3ehi4]
    · linarith only [h10, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem n7l_sBT3_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have h3elo := hb3.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
    · linarith only [h8, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h11, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
    · linarith only [h14, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h14, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
    · linarith only [h18, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h18, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
    · linarith only [h22, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h22, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
    · linarith only [h25, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h25, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h34 | h34
    · linarith only [h34, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h34, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · linarith only [h37, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h37, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
    · linarith only [h8, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h11, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
    · linarith only [h14, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h14, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
    · linarith only [h18, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h18, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
    · linarith only [h22, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h22, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
    · linarith only [h25, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h25, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
    · linarith only [h29, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h29, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
    · linarith only [h32, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h32, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h36 | h36
    · linarith only [h36, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h36, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h43 | h43
    · linarith only [h43, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h43, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
    · linarith only [h46, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h46, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have h3ehi := hb3.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h8 | h8
    · linarith only [h8, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
    · linarith only [h12, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h12, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h16 | h16
    · linarith only [h16, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h16, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u3ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h21 | h21
    · linarith only [h21, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h21, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h25, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h28 | h28
    · linarith only [h28, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h28, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
    · linarith only [h32, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h32, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h36, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h39 | h39
    · linarith only [h39, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h39, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht34, p0_1, u3ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo0]

theorem n7l_sBT3_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo0]

theorem n7l_sBT3_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo0]

theorem n7l_sBT3_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h3elo := hb3.1
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]

theorem n7l_sBT3_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h1, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h3, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h1, h10, h4, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h1, h10, h12, h6, h9, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h0, h1, h12, h9, hc34, hc45, hlam, hphi]
              · linarith only [h3, h4, h9, hc13, hc35, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h4, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h1, h16, h17, h19, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h0, h1, h16, h19, hc34, hc45, hlam, hphi]
              · linarith only [h16, h3, h4, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h23 | h23
        · linarith only [h23, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
          · linarith only [h25, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h1, h28, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h1, h23, h30, hc15, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h25, h3, h32, hc14, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h1, h27, h3, h32, h34, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h0, h1, h27, h32, h36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                        · linarith only [h0, h1, h32, h38, hc13, hc34, hlam, hphi]
                        · linarith only [h3, h38, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
              · linarith only [h0, h3, h41, hlam, hphi, u0ehi7, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h1, h43, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                  · linarith only [h25, h3, h45, hc14, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                    · linarith only [h3, h47, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h47, h49, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                        · linarith only [h0, h1, h27, h45, h51, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h3, h51, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
    · linarith only [h54, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
      · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
        · linarith only [h57, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h59 | h59
          · linarith only [h59, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
            · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
              · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h57, h61, h63, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h63, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
              · linarith only [h0, h56, h62, hlam, hphi, u0ehi5, u0elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
              · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                · linarith only [h57, h68, hc13, hlam, hphi, ht01, u0ehi7]
                · linarith only [h0, h68, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
              · linarith only [h0, h56, h67, hlam, hphi, u0ehi5, u0elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
        · linarith only [h56, h72, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
          · linarith only [h74, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
              · linarith only [h56, h76, h77, hc12, hlam, hphi, ht01, u0ehi7]
              · linarith only [h0, h77, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
              · linarith only [h0, h56, h80, hc13, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h80, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]

theorem n7l_sBT3_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
        · linarith only [h0, h5, hc13, hlam, hphi, ht01, u0ehi7]
        · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
        · linarith only [h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
          · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
            · linarith only [h0, h11, hc23, hlam, hphi, ht01, ht12, u0ehi7]
            · linarith only [h10, h11, h4, hc35, hlam, hphi, u3ehi1]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
            · linarith only [h10, h14, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
              · linarith only [h16, h2, hc24, hlam, hphi, ht01, ht12, u0ehi8]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h10, h16, h18, hc34, hlam, hphi, u3ehi2]
                · linarith only [h18, h4, hc45, hlam, hphi, ht34, u3ehi1]

theorem n7l_sBT3_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
      · linarith only [h1, h2, hc13, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem n7l_sBT3_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h3elo := hb3.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9, u3elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT3_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h4, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h2, h4, h8, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h2, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h12, h2, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                  · linarith only [h12, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
        · linarith only [h2, h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16 | h16
        · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
          · linarith only [h16, h17, h2, hc12, hlam, hphi, ht01, u0ehi9]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
            · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                · linarith only [h1, h21, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h17, h19, h21, hlam]
              · linarith only [h19, h20, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                · linarith only [h1, h26, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h1, h28, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                  · linarith only [h28, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h16, h2, h25, hc12, hc23, hlam, hphi]
        · linarith only [h16, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h33 | h33
      · linarith only [h0, h1, h33, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
        · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
          · linarith only [h33, h36, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
            · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                    · linarith only [h0, h38, h42, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h1, h36, h38, h40, h42, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h41, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h0, h1, h38, h40, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h38, h39, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
              · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                      · linarith only [h0, h48, h52, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · linarith only [h0, h1, h36, h48, h50, h52, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h1, h36, h48, h49, h50, h51, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h1, h50, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h0, h1, h35, h49, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
              · linarith only [h0, h1, h35, h36, h48, hc12, hc23, hlam, hphi]
        · linarith only [h35, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h60 | h60
    · rcases m.htr 0 2 3 (by decide) (by decide) with h61 | h61
      · rcases m.htr 0 2 5 (by decide) (by decide) with h62 | h62
        · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
          · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
            · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
              · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                · linarith only [h60, h66, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h60, h68, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h68, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h0, h62, h65, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h60, h63, h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h60, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h61, h62, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · linarith only [h0, h60, h61, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h76 | h76
      · rcases m.htr 0 2 5 (by decide) (by decide) with h77 | h77
        · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
          · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
            · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
              · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                    · linarith only [h76, h83, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h78, h81, h83, h85, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h85, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                  · linarith only [h82, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h60, h81, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
              · linarith only [h0, h77, h80, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h60, h78, h79, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h78, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h76, h77, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h94 | h94
        · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
          · linarith only [h0, h76, h95, hc12, hlam, hphi, ht01, u0ehi5]
          · linarith only [h0, h95, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h0, h94, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]

theorem n7l_sBT3_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
          · linarith only [h2, h5, hc13, hlam, hphi, u3elo2]
          · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
        · linarith only [h1, h4, hc23, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem n7l_sBT3_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h5, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h1, h12, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                  · linarith only [h12, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h11, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h3, h4, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h18, h19, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h22, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h1, h17, h24, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h1, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                  · linarith only [h17, h18, h26, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · linarith only [h17, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
      · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
        · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · linarith only [h1, h31, h34, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h36, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h1, h31, h36, hc12, hc23, hlam, hphi]
          · linarith only [h1, h31, h33, hlam, hphi, u5ehi7, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
            · linarith only [h1, h31, h41, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
              · linarith only [h0, h43, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
              · linarith only [h1, h31, h43, hc12, hc23, hlam, hphi]
          · linarith only [h1, h31, h40, hlam, hphi, u5ehi7, u5elo3]
      · linarith only [h31, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h48 | h48
    · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
      · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
        · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
          · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
            · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
              · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h48, h55, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · linarith only [h51, h54, h55, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                  · linarith only [h48, h50, h54, h58, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h48, h50, h54, h60, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h48, h50, h60, h62, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h54, h62, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h53, hc25, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h52, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h51, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                · linarith only [h48, h50, h68, h71, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                  · linarith only [h48, h73, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · linarith only [h50, h68, h73, hc23, hc34, hlam, hphi]
              · linarith only [h0, h49, h70, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h69, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h68, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
      · linarith only [h48, h49, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h80 | h80
      · rcases m.htr 0 3 4 (by decide) (by decide) with h81 | h81
        · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
          · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
            · linarith only [h0, h48, h83, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h83, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h48, h80, h82, hlam, hphi, u5ehi7, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h87 | h87
          · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
            · linarith only [h0, h48, h88, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h88, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h48, h80, h87, hlam, hphi, u5ehi7, u5elo3]
      · linarith only [h0, h80, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]

theorem n7l_sBT3_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
            · linarith only [h5, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h2, h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo1]
        · linarith only [h0, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
    · linarith only [h0, h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc13, hlam, hphi, ht01, u0ehi7]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
      · linarith only [h12, h14, hc34, hlam, hphi, u3ehi4]
      · linarith only [h14, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]

end R2N4
