import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h2, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h2, h6, hc13, hlam, hphi, u3elo0]
            · linarith only [h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h3, h4, hlam]
              · linarith only [h13, h2, hc13, hlam, hphi, u3elo0]
            · linarith only [h12, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h17, h20, h22, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h22, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h17, h20, h21, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h17, h20, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h19, h2, hc13, hlam, hphi, u3elo0]
            · linarith only [h17, h18, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
            · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
              · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                    · linarith only [h1, h30, h33, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h33, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h17, h31, h32, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h2, h31, hc23, hlam, hphi, u3elo0]
              · linarith only [h2, h30, hc13, hlam, hphi, u3elo0]
            · linarith only [h29, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
        · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
          · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
              · linarith only [h2, h43, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                · linarith only [h1, h2, h40, h45, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                  · linarith only [h0, h41, h45, h47, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h47, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h40, h42, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
              · linarith only [h1, h2, h52, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                · linarith only [h1, h2, h40, h54, hlam]
                · linarith only [h40, h41, h54, hc23, hlam, hphi, u3elo3]
            · linarith only [h40, h51, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
          · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
            · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
              · linarith only [h1, h2, h60, hlam]
              · linarith only [h40, h58, h60, hlam]
            · linarith only [h58, h59, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
            · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
              · linarith only [h1, h2, h65, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                · linarith only [h2, h67, hc03, hlam, hphi, u3elo2]
                · linarith only [h40, h64, h67, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
            · linarith only [h64, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
    · rcases m.htr 0 3 4 (by decide) (by decide) with h73 | h73
      · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
        · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
          · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
              · linarith only [h0, h72, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h73, h74, h77, hc23, hlam, hphi, u3elo0]
            · linarith only [h0, h72, h74, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h0, h72, h74, h75, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
        · linarith only [h0, h74, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
        · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
            · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
              · linarith only [h72, h73, h86, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                · linarith only [h0, h72, h83, h84, h86, h88, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h72, h83, h90, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h90, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h0, h72, h83, h85, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h0, h72, h83, h84, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
        · linarith only [h0, h72, h83, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h96 | h96
      · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
        · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
          · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
              · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h101, h103, h97, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h103, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h101, h102, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h101, h96, hc23, hlam, hphi, u3elo0]
              · linarith only [h100, h72, h96, hlam]
            · linarith only [h0, h99, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h98, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h97, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
        · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
          · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
            · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
              · linarith only [h115, h96, hc03, hlam, hphi, u3elo1]
              · linarith only [h115, h72, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h112, h114, h72, hc01, hlam, hphi, ht12, u2elo4]
          · linarith only [h112, h113, h72, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h112, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · linarith only [h4, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h3, h5, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, h4, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h1, h14, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h10, h16, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h1, h13, h16, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h13, h19, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                    · linarith only [h0, h10, h21, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h0, h10, h19, h23, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h23, h3, h4, hc23, hlam, hphi, u3elo4]
            · linarith only [h10, h3, h4, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h27 | h27
          · linarith only [h27, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
            · linarith only [h29, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
              · linarith only [h0, h27, h3, h31, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h1, h34, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h34, h37, hc13, hlam, hphi, u3elo2]
                      · linarith only [h3, h37, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h2, h3, h33, h34, h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h33, h41, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                    · linarith only [h33, h43, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h3, h43, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h46 | h46
        · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h2, h47, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
            · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
              · linarith only [h0, h2, h47, h50, hlam]
              · linarith only [h0, h2, h49, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h46, h49, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h54 | h54
          · linarith only [h46, h54, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
            · linarith only [h0, h46, h56, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
              · linarith only [h0, h46, h54, h58, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
              · linarith only [h1, h2, h56, h58, hc12, hlam, hphi, u2elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h62 | h62
    · rcases m.htr 0 1 5 (by decide) (by decide) with h63 | h63
      · linarith only [h0, h63, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h65 | h65
        · rcases m.htr 0 2 5 (by decide) (by decide) with h66 | h66
          · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
            · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
              · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                · linarith only [h62, h63, h68, h69, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h62, h63, h68, h71, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                  · linarith only [h62, h63, h67, h71, hc23, hlam, hphi, u3elo4]
              · linarith only [h66, h68, hc12, hlam, hphi, u2elo0]
            · linarith only [h0, h66, h67, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
              · linarith only [h66, h77, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h77, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h0, h62, h76, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h62, h65, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
      · linarith only [h62, h82, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h84 | h84
        · rcases m.htr 0 2 5 (by decide) (by decide) with h85 | h85
          · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
            · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
              · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h84, h91, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                      · linarith only [h89, h91, hc23, hlam, hphi, u3elo1]
                    · linarith only [h88, h90, hc23, hlam, hphi, u3elo1]
                  · linarith only [h62, h89, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h62, h88, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h85, h87, hlam]
            · linarith only [h0, h85, h86, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
              · linarith only [h100, h85, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h100, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h0, h84, h99, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h104 | h104
          · linarith only [h104, h84, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
            · linarith only [h106, h84, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h106, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_10_12_13_25_L_I_L_R_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h12, h13, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h13, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h12, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h11, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h5, h7, hlam, hphi, ht23, u2ehi1, u3elo0]
                    · linarith only [h9, hlam, hphi, ht23, u2ehi1, u3elo2]
                  · linarith only [h5, h8, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h4, h7, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h6, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · linarith only [h4, hlam, hphi, ht23, u2ehi0, u3elo2]
        · linarith only [h0, h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h26 | h26
        · rcases m.htr 0 2 3 (by decide) (by decide) with h27 | h27
          · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
            · linarith only [h0, h2, h28, hlam]
            · linarith only [h27, h28, hc24, hlam, hphi, u2ehi2]
          · linarith only [h27, hlam, hphi, ht23, u2ehi0, u3elo2]
        · linarith only [h0, h26, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
    · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
      · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 2 3 (by decide) (by decide) with h37 | h37
          · rcases m.htr 0 2 4 (by decide) (by decide) with h38 | h38
            · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                            · linarith only [h0, h34, h43, h44, h46, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h46, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h45, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h40, h44, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h36, h43, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                    · linarith only [h0, h42, hlam, hphi, ht23, u2ehi0, u3elo2]
                  · linarith only [h38, h41, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h37, h40, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h37, h39, hc25, hlam, hphi, u2ehi2]
            · linarith only [h37, h38, hc24, hlam, hphi, u2ehi2]
          · linarith only [h37, hlam, hphi, ht23, u2ehi0, u3elo2]
        · linarith only [h34, h36, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h59 | h59
        · rcases m.htr 0 2 3 (by decide) (by decide) with h60 | h60
          · rcases m.htr 0 2 4 (by decide) (by decide) with h61 | h61
            · rcases m.htr 0 2 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h34, h35, h63, hlam]
                · linarith only [h60, h63, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h60, h62, hc25, hlam, hphi, u2ehi2]
            · linarith only [h60, h61, hc24, hlam, hphi, u2ehi2]
          · linarith only [h60, hlam, hphi, ht23, u2ehi0, u3elo2]
        · linarith only [h34, h59, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h70 | h70
      · rcases m.htr 0 1 5 (by decide) (by decide) with h71 | h71
        · linarith only [h34, h71, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi6]
        · linarith only [h70, h71, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
        · linarith only [h34, h74, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h76 | h76
          · rcases m.htr 0 2 4 (by decide) (by decide) with h77 | h77
            · rcases m.htr 0 2 5 (by decide) (by decide) with h78 | h78
              · rcases m.htr 0 3 4 (by decide) (by decide) with h79 | h79
                · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h76, h84, h86, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · rcases h0bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h34, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h70, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h74, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  rcases p88_3 (m.d 0 1) (by simp) with h94 | h94
                                  · linarith only [h0, h94, hlam]
                                  · rcases p88_3 (m.d 0 2) (by simp) with h96 | h96
                                    · rcases p88_3 (m.d 0 3) (by simp) with h97 | h97
                                      · linarith only [h76, h97, hlam]
                                      · linarith only [h34, h97, hlam]
                                    · linarith only [h0, h96, hlam]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h77, h79, h85, h86, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h77, h85, h86, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  rcases p88_3 (m.d 0 1) (by simp) with h104 | h104
                                  · linarith only [h0, h104, hlam]
                                  · rcases p88_3 (m.d 0 2) (by simp) with h106 | h106
                                    · rcases p88_3 (m.d 0 3) (by simp) with h107 | h107
                                      · linarith only [h107, h76, hlam]
                                      · linarith only [h0, h107, h77, h79, h85, h86, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p88_1]
                                    · linarith only [h106, h78, hlam]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p88_1, u3elo0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h76, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h34, h77, h85, h86, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p88_1, u3elo1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h34, h78, hlam, hphi, ht23, p88_1, u2ehi4, u3elo1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h34, h79, hc01, hlam, hphi, ht12, ht23, p88_1, u3elo1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h77, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h79, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h34, h78, h79, hlam, hphi, ht23, p88_1, u2ehi4, u3elo1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p88_1, u5elo0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h78, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h74, h77, h79, h85, h86, hc34, hlam, hphi, ht45, p88_1, u5elo1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h80, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                            · linarith only [h85, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h84, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h34, h79, h83, hlam]
                      · linarith only [h0, h76, h82, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h76, h81, hlam]
                  · linarith only [h77, h80, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h76, h79, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h76, h78, hc25, hlam, hphi, u2ehi2]
            · linarith only [h76, h77, hc24, hlam, hphi, u2ehi2]
          · linarith only [h76, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h0emin := hb0.2.2
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h2, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                        · rcases h0emin with h14 | h14 | h14 | h14 | h14
                          · rcases h5bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h10, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p15_1, u2elo0, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h10, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p15_1, u2elo0, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
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
                              linarith only [h10, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h1, h10, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p15_1, u2elo0, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h1, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h4, hlam, p15_1]
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
                              linarith only [h10, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo4]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h13, hc34, hlam, hphi, ht01, ht12, ht23, p15_1, u0ehi4]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h10, h13, h7, hc34, hlam, hphi, p15_1, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h10, h13, hc34, hlam, hphi, p15_1, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              rcases p15_3 (m.d 0 5) (by simp) with h35 | h35
                              · linarith only [h35, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                              · linarith only [h35, h5, hlam]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h5, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h10, h7, hc45, hlam, hphi, ht34, p15_1, u3ehi2]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h12, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h13, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                          · linarith only [h14, hlam, ht01, ht12, u2elo0]
                          · linarith only [h14, h2, hlam, ht01, ht12, u2elo0]
                          · linarith only [h14, h3, hlam, ht01, ht12, u2elo0]
                          · linarith only [h14, h3, h5, hlam, ht01, ht12, u2elo0]
                        · linarith only [h0, h12, h13, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h12, h3, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                · linarith only [h4, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h3, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                  · linarith only [h2, h53, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h53, h55, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h0, h5, h51, h57, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                        · linarith only [h5, h59, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h53, h59, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h4, h52, hc12, hlam, hphi, u2elo0]
              · linarith only [h3, h51, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 2 4 (by decide) (by decide) with h68 | h68
        · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
          · linarith only [h0, h1, h69, hlam]
          · linarith only [h67, h69, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
        · linarith only [h67, h68, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
      · linarith only [h67, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_10_12_13_25_L_R_L_I_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h10, h4, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h15, h6, h9, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h15, h4, hc23, hlam, hphi, u3elo0]
                  · linarith only [h3, h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h20, h21, h6, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi8]
                      · linarith only [h21, h4, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h20, h24, h6, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h24, h4, hc23, hlam, hphi, u3elo0]
                  · linarith only [h19, h3, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h2, h29, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                  · linarith only [h28, h29, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h2, h32, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                            · linarith only [h2, h35, h38, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi9]
                            · rcases h2bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                rcases p40_3 (m.d 0 2) (by simp) with h42 | h42
                                · rcases p40_3 (m.d 1 2) (by simp) with h43 | h43
                                  · linarith only [h0, h43, hlam]
                                  · rcases p40_3 (m.d 2 3) (by simp) with h45 | h45
                                    · linarith only [h2, h45, hlam]
                                    · linarith only [h45, h6, hlam]
                                · linarith only [h0, h42, hlam]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h34, h6, hc01, hlam, hphi, ht0b, ht5b, p40_1, u5ehi8]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h37, h38, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                rcases p40_3 (m.d 0 2) (by simp) with h51 | h51
                                · rcases p40_3 (m.d 1 2) (by simp) with h52 | h52
                                  · linarith only [h0, h52, hlam]
                                  · rcases p40_3 (m.d 2 3) (by simp) with h54 | h54
                                    · linarith only [h2, h54, hlam]
                                    · linarith only [h36, h54, hlam]
                                · linarith only [h51, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h6, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h28, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h32, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, p40_1, u3elo2]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, h37, h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p40_1, u3elo0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, h32, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40_1, u3elo0, u5ehi6]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p40_1, u0ehi1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, h35, hc12, hlam, hphi, ht23, p40_1, u3elo0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h35, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, h32, h35, hc12, hlam, hphi, ht23, p40_1, u3elo0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h3, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p40_1, u5elo2]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h36, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h37, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                          · linarith only [h28, h37, h4, h5, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h34, h36, h6, hlam]
                      · linarith only [h34, h35, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                        · linarith only [h34, h82, hc13, hlam, hphi, u3elo2]
                        · linarith only [h81, h82, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h6, h81, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h91 | h91
    · rcases m.htr 0 2 3 (by decide) (by decide) with h92 | h92
      · rcases m.htr 0 2 5 (by decide) (by decide) with h93 | h93
        · rcases m.htr 0 3 4 (by decide) (by decide) with h94 | h94
          · rcases m.htr 0 4 5 (by decide) (by decide) with h95 | h95
            · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h0, h91, h99, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                      · linarith only [h101, h96, h99, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h101, h94, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h98, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h91, h94, h95, h97, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h0, h91, h94, h95, h96, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · linarith only [h95, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
          · linarith only [h94, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h92, h93, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h91, h92, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
    · linarith only [h91, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_12_13_25_L_R_L_R_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases h5bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hlam, hphi, ht23, p8_1, u2ehi4, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8_1, u2ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc25, hlam, hphi, ht01, ht12, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h3, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h1, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h4, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h7, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, hc04, hc35, hlam, hphi, ht0b, ht5b, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                · linarith only [h0, h1, h5, h7, hlam, hphi, ht23, u2ehi3, u3elo0]
              · linarith only [h6, hlam, hphi, ht23, u2ehi2, u3elo4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
              · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                · linarith only [h3, h37, h5, hlam]
                · linarith only [h1, h2, h37, hlam, hphi, ht23, u2ehi3, u3elo0]
              · linarith only [h1, h36, hc23, hlam, hphi, u3elo0]
          · linarith only [h1, h4, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
              · linarith only [h3, h44, hlam, hphi, ht23, u2ehi1, u3elo2]
              · linarith only [h1, h44, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
              · linarith only [h3, h47, hlam, hphi, ht23, u2ehi1, u3elo2]
              · linarith only [h1, h47, hc23, hlam, hphi, u3elo0]
          · linarith only [h1, h42, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
        · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
          · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
            · linarith only [h2, h53, hc14, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
              · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                · linarith only [h2, h56, hc24, hlam, hphi, ht01, ht12, u0ehi3]
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
                    linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h1, h56, hlam, hphi, ht23, p58_1, u2ehi3, u3elo0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h2, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h56, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi3]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h53, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h51, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h51, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h51, h52, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p58_1, u3elo1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h56, hlam, p58_1]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h1, hlam, p58_0]
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
                    linarith only [hlam, p58_0]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h2, hlam, hphi, ht01, ht12, ht23, p58_1, u0ehi3, u3elo4]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p58_1, u0ehi4]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [h51, hc45, hlam, hphi, ht23, ht34, p58_1, u2ehi4]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hc45, hlam, hphi, ht23, ht34, p58_1, u2ehi4]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    rcases p58_3 (m.d 0 5) (by simp) with h82 | h82
                    · linarith only [h2, h82, hlam]
                    · linarith only [h1, h82, hlam]
                  · have p58_0 := h58c.1
                    have p58_1 := h58c.2.1
                    have p58_2 := h58c.2.2.1
                    have p58_3 := h58c.2.2.2
                    linarith only [hlam, p58_0]
              · linarith only [h55, hlam, hphi, ht23, u2ehi2, u3elo4]
          · linarith only [h1, h52, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
          · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
            · linarith only [h2, h89, hc14, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
              · linarith only [h51, h91, hlam, hphi, ht23, u2ehi1, u3elo2]
              · linarith only [h1, h91, hc23, hlam, hphi, u3elo0]
          · linarith only [h1, h88, hc13, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
    · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
      · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
          · linarith only [h0, h99, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
          · linarith only [h96, h99, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
          · linarith only [h0, h102, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
          · linarith only [h102, h96, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
        · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
          · linarith only [h0, h106, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
          · linarith only [h106, h96, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
          · linarith only [h0, h109, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
          · linarith only [h109, h96, hc13, hlam, hphi, u3elo0]
    · linarith only [h96, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]

theorem r1l7_10_12_13_25_L_R_L_R_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
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
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h13, hlam, hphi, ht23, u2ehi2, u3elo4]
                          · linarith only [h12, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h11, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h4, h5, h7, hlam, hphi, ht23, u2ehi1, u3elo0]
                    · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h8, hlam, hphi, ht23, u2ehi1, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                            · linarith only [h0, h21, h26, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h26, hlam, hphi, ht23, u2ehi2, u3elo4]
                          · linarith only [h25, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h24, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h23, h4, h6, hlam, hphi, ht23, u2ehi1, u3elo0]
                    · linarith only [h21, h22, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h21, hlam, hphi, ht23, u2ehi1, u3elo2]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · linarith only [h3, h4, hc25, hlam, hphi, u2ehi2]
        · linarith only [h3, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h38 | h38
        · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
          · linarith only [h0, h2, h39, hlam]
          · linarith only [h38, h39, hc25, hlam, hphi, u2ehi2]
        · linarith only [h38, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h44 | h44
    · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
      · rcases m.htr 0 2 3 (by decide) (by decide) with h46 | h46
        · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
          · rcases m.htr 0 3 4 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 3 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                        · linarith only [h0, h44, h54, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h51, h54, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h0, h44, h51, h53, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h44, h51, h52, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h45, h51, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h0, h44, h63, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h60, h63, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h0, h44, h60, h62, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h44, h60, h61, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h45, h60, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h48, h49, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
            · linarith only [h48, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · linarith only [h46, h47, hc25, hlam, hphi, u2ehi2]
        · linarith only [h46, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h73 | h73
        · rcases m.htr 0 2 5 (by decide) (by decide) with h74 | h74
          · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
              · linarith only [h44, h45, h76, hlam]
              · linarith only [h75, h76, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
            · linarith only [h75, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · linarith only [h73, h74, hc25, hlam, hphi, u2ehi2]
        · linarith only [h73, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h44, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_12_23_L_0_L_I_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h0, h2, h3, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h3, hc12, hlam, hphi, ht23, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
          · linarith only [h0, h11, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
            · linarith only [h0, h10, h13, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h13, hc23, hlam, hphi, u3elo3]
        · linarith only [h10, hc12, hlam, hphi, ht23, u3elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h18 | h18
    · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
      · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
        · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h18, h22, h25, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h18, h22, h24, h25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h24, h28, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · rcases h2bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h0, hlam, p30_1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h23, hc35, hlam, hphi, ht0b, ht5b, p30_1, u0elo1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      rcases p30_3 (m.d 0 2) (by simp) with h34 | h34
                      · rcases p30_3 (m.d 1 2) (by simp) with h35 | h35
                        · rcases p30_3 (m.d 2 3) (by simp) with h36 | h36
                          · linarith only [h18, h36, hlam]
                          · linarith only [h22, h36, hlam]
                        · linarith only [h0, h18, h23, h24, h28, h35, hc34, hc45, hlam, hphi]
                      · linarith only [h34, hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      rcases p30_3 (m.d 0 2) (by simp) with h41 | h41
                      · rcases p30_3 (m.d 1 2) (by simp) with h42 | h42
                        · rcases p30_3 (m.d 2 3) (by simp) with h43 | h43
                          · linarith only [h18, h43, hlam]
                          · linarith only [h23, h43, hlam]
                        · linarith only [h21, h42, hlam]
                      · linarith only [h41, hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h18, h23, h28, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p30_1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      rcases p30_3 (m.d 0 2) (by simp) with h50 | h50
                      · linarith only [h0, h50, hlam]
                      · linarith only [h18, h50, hlam]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      rcases p30_3 (m.d 0 2) (by simp) with h53 | h53
                      · linarith only [h0, h53, hlam]
                      · linarith only [h19, h24, h53, hlam]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      rcases p30_3 (m.d 0 2) (by simp) with h56 | h56
                      · linarith only [h0, h56, hlam]
                      · linarith only [h19, h56, hlam]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h18, hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h20, hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p30_1, u3elo2]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p30_1, u3elo2]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h18, h22, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30_1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h0, h19, h23, h24, h28, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p30_1, u0elo4, u3elo2]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h22, hlam, p30_1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h24, hlam, p30_1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h19, hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h21, hlam, p30_0]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h23, hlam, p30_1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [h19, hc24, hlam, hphi, ht0b, ht45, ht5b, p30_1, u0elo1]
                    · have p30_0 := h30c.1
                      have p30_1 := h30c.2.1
                      have p30_2 := h30c.2.2.1
                      have p30_3 := h30c.2.2.2
                      linarith only [hlam, p30_0]
              · linarith only [h23, hc23, hlam, hphi, u3elo4]
            · linarith only [h22, hc23, hlam, hphi, u3elo3]
          · linarith only [h0, h19, h21, hlam]
        · linarith only [h0, h20, hc02, hlam, hphi, ht23, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
        · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
          · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
            · linarith only [h18, h19, h79, h80, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h80, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
            · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
              · linarith only [h18, h79, h84, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h84, hc23, hlam, hphi, u3elo4]
            · linarith only [h83, hc23, hlam, hphi, u3elo3]
        · linarith only [h0, h18, h78, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · linarith only [h18, hc02, hlam, hphi, ht23, u3elo2]

theorem r1l7_10_12_23_L_I_L_0_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
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
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h1, h11, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                        · linarith only [h11, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · linarith only [h10, hc23, hlam, hphi, u3elo4]
                    · linarith only [h4, h6, h9, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h8, hc13, hlam, hphi, u3elo3]
                · linarith only [h7, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h1, h19, h20, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h20, h23, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases h0bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h18, h22, h23, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 1) (by simp) with h28 | h28
                            · rcases p25_3 (m.d 0 2) (by simp) with h29 | h29
                              · linarith only [h0, h29, hlam]
                              · linarith only [h2, h29, hlam]
                            · linarith only [h1, h28, hlam]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 1) (by simp) with h33 | h33
                            · rcases p25_3 (m.d 0 2) (by simp) with h34 | h34
                              · linarith only [h0, h34, hlam]
                              · linarith only [h0, h18, h22, h23, h34, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h33, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 1) (by simp) with h38 | h38
                            · rcases p25_3 (m.d 0 2) (by simp) with h39 | h39
                              · linarith only [h0, h39, hlam]
                              · linarith only [h3, h39, hlam]
                            · linarith only [h38, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h1, h18, h22, h23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25_1, u2elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 1) (by simp) with h46 | h46
                            · rcases p25_3 (m.d 0 2) (by simp) with h47 | h47
                              · rcases p25_3 (m.d 0 3) (by simp) with h48 | h48
                                · linarith only [h2, h48, hlam]
                                · linarith only [h4, h48, hlam]
                              · linarith only [h47, hlam, p25_0]
                            · linarith only [h0, h18, h22, h23, h46, h6, hc34, hc45, hlam, hphi]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            rcases p25_3 (m.d 0 1) (by simp) with h53 | h53
                            · rcases p25_3 (m.d 0 2) (by simp) with h54 | h54
                              · rcases p25_3 (m.d 0 3) (by simp) with h55 | h55
                                · linarith only [h2, h55, hlam]
                                · linarith only [h5, h55, hlam]
                              · linarith only [h3, h54, hlam]
                            · linarith only [h0, h18, h22, h23, h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25_1, u2elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h1, hlam, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h2, hlam, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p25_1, u3elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p25_1, u3elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h18, h22, h23, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h18, h22, h23, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h4, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h6, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h0, h18, h22, h23, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p25_1, u3elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h3, hlam, p25_1]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h5, hlam, p25_0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p25_1, u3elo0]
                          · have p25_0 := h25c.1
                            have p25_1 := h25c.2.1
                            have p25_2 := h25c.2.2.1
                            have p25_3 := h25c.2.2.2
                            linarith only [hlam, p25_0]
                      · linarith only [h22, hc23, hlam, hphi, u3elo4]
                  · linarith only [h19, hc13, hlam, hphi, u3elo3]
                · linarith only [h18, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h5, hc03, hlam, hphi, u3elo4]
          · linarith only [h2, h4, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h80 | h80
          · rcases m.htr 0 3 5 (by decide) (by decide) with h81 | h81
            · linarith only [h2, h3, h81, hc23, hlam, hphi, u3elo0]
            · linarith only [h81, hc03, hlam, hphi, u3elo4]
          · linarith only [h1, h80, hc13, hlam, hphi, u3elo3]
      · linarith only [h2, hc02, hlam, hphi, ht23, u3elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h87 | h87
    · rcases m.htr 0 2 3 (by decide) (by decide) with h88 | h88
      · rcases m.htr 0 2 5 (by decide) (by decide) with h89 | h89
        · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
          · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
              · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
                · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                  · linarith only [h0, h87, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h94, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h93, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h0, h87, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h98, h99, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h98, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h91, hc03, hlam, hphi, u3elo4]
          · linarith only [h88, h90, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h105 | h105
          · rcases m.htr 0 3 5 (by decide) (by decide) with h106 | h106
            · linarith only [h0, h106, h87, h89, hc13, hlam, hphi, u3elo0]
            · linarith only [h106, hc03, hlam, hphi, u3elo4]
          · linarith only [h105, h87, hc13, hlam, hphi, u3elo3]
      · linarith only [h0, h87, h88, hc13, hlam, hphi, u3elo2]
    · linarith only [h87, hc01, hlam, hphi, ht12, ht23, u3elo1]

theorem r1l7_10_12_23_L_I_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h7, h9, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h2, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h11, hc34, hlam, hphi, u3ehi1]
              · linarith only [h4, h6, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h5, hc35, hlam, hphi, u3ehi0]
          · linarith only [h1, h4, hc34, hlam, hphi, u3ehi1]
        · linarith only [h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h18 | h18
        · linarith only [h18, h2, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
          · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
            · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h18, h25, hc25, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                    · linarith only [h1, h27, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h20, h27, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h20, h22, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h21, hc35, hlam, hphi, u3ehi0]
          · linarith only [h20, hc34, hlam, hphi, u3ehi0]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h33 | h33
      · linarith only [h0, h1, h33, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
        · linarith only [h33, h35, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
          · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
            · rcases m.htr 0 4 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                · linarith only [h33, h37, h40, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h1, h40, hc23, hlam, hphi, u2ehi1]
              · linarith only [h37, h39, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h37, h38, hc35, hlam, hphi, u3ehi3]
          · linarith only [h37, hc34, hlam, hphi, u3ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h46 | h46
    · linarith only [h0, h46, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h48 | h48
      · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
          · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                      · linarith only [h48, h56, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h50, h56, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h46, h55, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h0, h48, h54, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h48, h50, h53, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h50, h52, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h50, h51, hc35, hlam, hphi, u3ehi3]
          · linarith only [h50, hc34, hlam, hphi, u3ehi0]
        · linarith only [h48, h49, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h66 | h66
        · linarith only [h48, h66, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
          · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
            · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                · linarith only [h48, h68, h71, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h71, h73, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                          · rcases h0bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h0, hlam, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h46, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h0, h69, h70, h73, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u3ehi4]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h0, h69, h73, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u3ehi4]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h66, hc01, hc25, hlam, hphi, ht12, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h48, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h66, h70, hlam, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h66, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              rcases p79_3 (m.d 0 1) (by simp) with h90 | h90
                              · linarith only [h46, h90, hlam]
                              · rcases p79_3 (m.d 0 2) (by simp) with h92 | h92
                                · linarith only [h48, h92, hlam]
                                · linarith only [h0, h92, hlam]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h48, hc23, hlam, hphi, p79_1, u2ehi0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h48, h69, h70, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u3ehi4]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h48, h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u3ehi4]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              rcases p79_3 (m.d 0 1) (by simp) with h99 | h99
                              · linarith only [h99, hlam, p79_0]
                              · rcases p79_3 (m.d 0 2) (by simp) with h101 | h101
                                · linarith only [h0, h101, h73, h76, hc01, hc23, hlam, hphi, ht12, p79_1]
                                · linarith only [h0, h101, hlam]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h46, h68, h71, hc23, hlam, hphi, p79_1, u2ehi0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h68, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h46, h68, h69, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u3ehi4]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              rcases p79_3 (m.d 0 1) (by simp) with h108 | h108
                              · linarith only [h108, hlam, p79_0]
                              · rcases p79_3 (m.d 0 2) (by simp) with h110 | h110
                                · linarith only [h110, h66, hlam]
                                · linarith only [h0, h110, hlam]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h66, h77, hc23, hlam, hphi, p79_1, u2ehi0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h69, hlam, p79_0]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [h70, hlam, p79_1]
                            · have p79_0 := h79c.1
                              have p79_1 := h79c.2.1
                              have p79_2 := h79c.2.2.1
                              have p79_3 := h79c.2.2.2
                              linarith only [hlam, p79_0]
                          · linarith only [h78, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h46, h71, h77, hc35, hlam, hphi, u3ehi0]
                      · linarith only [h46, h68, h71, h76, hlam]
                    · linarith only [h46, h68, h75, hlam]
              · linarith only [h68, h70, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h68, h69, hc35, hlam, hphi, u3ehi3]
          · linarith only [h68, hc34, hlam, hphi, u3ehi0]

end R2N4
