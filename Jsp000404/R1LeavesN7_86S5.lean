import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_14_H_I_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
            · rcases h0emin with h7 | h7 | h7 | h7 | h7
              · linarith only [h7, hlam, ht01, u1elo0]
              · linarith only [h0, h7, hlam, ht01, u1elo0]
              · linarith only [h1, h7, hlam, ht01, u1elo0]
              · linarith only [h1, h4, h7, hlam, ht01, u1elo0]
              · linarith only [h3, h7, hlam, ht01, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases h0emin with h15 | h15 | h15 | h15 | h15
              · linarith only [h15, hlam, ht01, u1elo0]
              · linarith only [h0, h15, hlam, ht01, u1elo0]
              · linarith only [h15, h4, hc34, hlam, ht01, ht12, ht23]
              · linarith only [h15, h2, hlam, ht01, u1elo0]
              · linarith only [h15, h3, hlam, ht01, u1elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
          · linarith only [h1, h2, h23, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
            · linarith only [h1, h2, h23, h25, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · rcases h0emin with h27 | h27 | h27 | h27 | h27
              · linarith only [h2, h27, hlam, ht01, u1elo3]
              · linarith only [h0, h2, h27, hlam, ht01, u1elo3]
              · linarith only [h1, h2, h27, hlam, ht01, u1elo3]
              · linarith only [h2, h27, hlam, ht01, u1elo3]
              · linarith only [h2, h22, h27, hlam, ht01, u1elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
          · linarith only [h1, h2, h33, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
            · linarith only [h1, h2, h33, h35, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
            · rcases h0emin with h37 | h37 | h37 | h37 | h37
              · linarith only [h2, h37, hlam, ht01, u1elo3]
              · linarith only [h0, h2, h37, hlam, ht01, u1elo3]
              · linarith only [h1, h2, h37, hlam, ht01, u1elo3]
              · linarith only [h2, h37, hlam, ht01, u1elo3]
              · linarith only [h22, h37, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h43 | h43
      · linarith only [h1, h43, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
        · rcases m.htr 0 3 4 (by decide) (by decide) with h46 | h46
          · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
            · rcases h0emin with h48 | h48 | h48 | h48 | h48
              · linarith only [h43, h47, h48, hlam, ht01, u1elo2]
              · linarith only [h0, h43, h47, h48, hlam, ht01, u1elo2]
              · linarith only [h1, h48, hlam, ht01, u1elo2]
              · linarith only [h1, h46, h48, hlam, ht01, u1elo2]
              · linarith only [h43, h45, h47, h48, hlam, ht01, u1elo2]
            · linarith only [h0, h1, h47, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
            · linarith only [h0, h1, h46, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h55, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
          · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
            · rcases h0emin with h60 | h60 | h60 | h60 | h60
              · linarith only [h43, h60, hlam, ht01, u1elo3]
              · linarith only [h0, h43, h60, hlam, ht01, u1elo3]
              · linarith only [h1, h60, hlam, ht01, u1elo2]
              · linarith only [h1, h58, h60, hlam, ht01, u1elo2]
              · linarith only [h45, h60, hlam, ht01, u1elo4]
            · linarith only [h0, h1, h59, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
            · linarith only [h0, h1, h58, h67, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h67, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h70 | h70
    · rcases m.htr 0 1 4 (by decide) (by decide) with h71 | h71
      · linarith only [h0, h71, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h73 | h73
        · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
          · linarith only [h0, h70, h74, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
            · linarith only [h0, h70, h74, h76, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · rcases h0emin with h78 | h78 | h78 | h78 | h78
              · linarith only [h0, h78, hlam, ht01, u1elo1]
              · linarith only [h0, h78, hlam, ht01, u1elo1]
              · linarith only [h0, h70, h78, hlam, ht01, u1elo1]
              · linarith only [h71, h78, hlam, ht01, u1elo3]
              · linarith only [h0, h73, h78, hlam, ht01, u1elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
          · linarith only [h0, h70, h84, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
            · linarith only [h0, h70, h84, h86, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
            · rcases h0emin with h88 | h88 | h88 | h88 | h88
              · linarith only [h0, h88, hlam, ht01, u1elo1]
              · linarith only [h0, h88, hlam, ht01, u1elo1]
              · linarith only [h0, h70, h88, hlam, ht01, u1elo1]
              · linarith only [h71, h88, hlam, ht01, u1elo3]
              · linarith only [h73, h88, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h94 | h94
      · linarith only [h0, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
        · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
          · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
            · rcases h0emin with h99 | h99 | h99 | h99 | h99
              · linarith only [h94, h98, h99, hlam, ht01, u1elo2]
              · linarith only [h0, h99, hlam, ht01, u1elo1]
              · linarith only [h70, h99, hlam, ht01, u1elo2]
              · linarith only [h70, h97, h99, hlam, ht01, u1elo2]
              · linarith only [h94, h96, h98, h99, hlam, ht01, u1elo2]
            · linarith only [h70, h97, h98, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
            · linarith only [h106, h70, h97, hc01, hlam, hphi, u1elo2]
            · rcases h0emin with h108 | h108 | h108 | h108 | h108
              · linarith only [h108, h70, hlam, ht01, u1elo2]
              · linarith only [h0, h108, hlam, ht01, u1elo1]
              · linarith only [h106, h108, h70, hlam, ht01, u1elo3]
              · linarith only [h108, h94, hlam, ht01, u1elo3]
              · linarith only [h106, h108, h70, h96, hlam, ht01, u1elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
          · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
            · rcases h0emin with h116 | h116 | h116 | h116 | h116
              · linarith only [h115, h116, h94, hlam, ht01, u1elo2]
              · linarith only [h0, h116, hlam, ht01, u1elo1]
              · linarith only [h116, h70, hlam, ht01, u1elo2]
              · linarith only [h114, h116, h70, hlam, ht01, u1elo2]
              · linarith only [h116, h96, hlam, ht01, u1elo4]
            · linarith only [h114, h115, h70, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
            · linarith only [h114, h123, h70, hc01, hlam, hphi, u1elo2]
            · rcases h0emin with h125 | h125 | h125 | h125 | h125
              · linarith only [h125, hlam, ht01, u1elo0]
              · linarith only [h0, h125, hlam, ht01, u1elo1]
              · linarith only [h123, h125, h70, hc34, hlam, ht01, ht12, ht23]
              · linarith only [h125, h94, hlam, ht01, u1elo3]
              · linarith only [h125, h96, hlam, ht01, u1elo4]

theorem r1l7_20_11_14_M_LI_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h4, h6, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
              · linarith only [h0, h3, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h11, h12, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h11, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                  · linarith only [h2, h20, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                  · linarith only [h16, h17, h18, h20, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi2]
              · linarith only [h17, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
              · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                  · linarith only [h16, h2, h27, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h16, h2, h25, h29, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h1, h29, h3, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h24, h3, h4, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
          · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
            · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
              · linarith only [h3, h33, h35, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
                · linarith only [h1, h35, h37, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h33, h37, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
              · linarith only [h3, h33, h40, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                · linarith only [h1, h40, h42, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h33, h42, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h45 | h45
            · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
              · linarith only [h0, h3, h46, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h33, h48, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h2, h50, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                  · linarith only [h45, h50, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h3, h53, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h33, h55, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h2, h45, h57, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h0, h33, h45, h59, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h33, h59, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
      · linarith only [h1, h2, hc14, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h64 | h64
    · linarith only [h0, h64, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
      · linarith only [h0, h66, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h68 | h68
        · rcases m.htr 0 2 4 (by decide) (by decide) with h69 | h69
          · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
            · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
              · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h69, h74, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · linarith only [h70, h74, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                  · linarith only [h66, h69, h70, h73, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                · linarith only [h0, h72, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h68, h71, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
              · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h66, h70, h82, hc14, hlam, hphi, u1ehi0]
                  · linarith only [h66, h82, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                · linarith only [h69, h81, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
              · linarith only [h0, h68, h80, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                · linarith only [h0, h69, h89, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h89, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h68, h88, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                · linarith only [h0, h69, h94, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h94, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h68, h93, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h98 | h98
          · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
              · linarith only [h100, h68, h98, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h100, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
              · linarith only [h0, h103, h68, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h103, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
              · linarith only [h0, h107, h68, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h107, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
              · linarith only [h0, h110, h68, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h110, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_20_11_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases h0emin with h4 | h4 | h4 | h4 | h4
          · linarith only [h4, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hlam, ht01, u1elo0]
          · linarith only [h1, h4, hlam, ht01, u1elo0]
          · linarith only [h2, h4, hlam, ht01, u1elo0]
          · linarith only [h3, h4, hlam, ht01, u1elo0]
        · rcases h0emin with h10 | h10 | h10 | h10 | h10
          · linarith only [h10, h3, hlam, ht01, u1elo4]
          · linarith only [h0, h10, h3, hlam, ht01, u1elo4]
          · linarith only [h1, h10, h3, hlam, ht01, u1elo4]
          · linarith only [h10, h2, h3, hlam, ht01, u1elo4]
          · linarith only [h10, h3, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
        · rcases h0emin with h17 | h17 | h17 | h17 | h17
          · linarith only [h17, h2, hlam, ht01, u1elo3]
          · linarith only [h0, h17, h2, hlam, ht01, u1elo3]
          · linarith only [h1, h17, h2, hlam, ht01, u1elo3]
          · linarith only [h17, h2, hlam, ht01, u1elo3]
          · linarith only [h16, h17, h2, hlam, ht01, u1elo3]
        · rcases h0emin with h23 | h23 | h23 | h23 | h23
          · linarith only [h2, h23, hlam, ht01, u1elo3]
          · linarith only [h0, h2, h23, hlam, ht01, u1elo3]
          · linarith only [h1, h2, h23, hlam, ht01, u1elo3]
          · linarith only [h2, h23, hlam, ht01, u1elo3]
          · linarith only [h16, h23, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
      · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
        · rcases h0emin with h31 | h31 | h31 | h31 | h31
          · linarith only [h1, h31, hlam, ht01, u1elo2]
          · linarith only [h0, h1, h31, hlam, ht01, u1elo2]
          · linarith only [h1, h31, hlam, ht01, u1elo2]
          · linarith only [h1, h29, h31, hlam, ht01, u1elo2]
          · linarith only [h1, h30, h31, hlam, ht01, u1elo2]
        · rcases h0emin with h37 | h37 | h37 | h37 | h37
          · linarith only [h1, h37, hlam, ht01, u1elo2]
          · linarith only [h0, h1, h37, hlam, ht01, u1elo2]
          · linarith only [h1, h37, hlam, ht01, u1elo2]
          · linarith only [h1, h29, h37, hlam, ht01, u1elo2]
          · linarith only [h30, h37, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h43 | h43
        · rcases h0emin with h44 | h44 | h44 | h44 | h44
          · linarith only [h1, h44, hlam, ht01, u1elo2]
          · linarith only [h0, h1, h44, hlam, ht01, u1elo2]
          · linarith only [h1, h44, hlam, ht01, u1elo2]
          · linarith only [h29, h44, hlam, ht01, u1elo3]
          · linarith only [h1, h43, h44, hlam, ht01, u1elo2]
        · rcases h0emin with h50 | h50 | h50 | h50 | h50
          · linarith only [h1, h50, hlam, ht01, u1elo2]
          · linarith only [h0, h1, h50, hlam, ht01, u1elo2]
          · linarith only [h1, h50, hlam, ht01, u1elo2]
          · linarith only [h29, h50, hlam, ht01, u1elo3]
          · linarith only [h43, h50, hlam, ht01, u1elo4]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h56 | h56
    · rcases m.htr 0 1 4 (by decide) (by decide) with h57 | h57
      · rcases m.htr 0 1 5 (by decide) (by decide) with h58 | h58
        · rcases h0emin with h59 | h59 | h59 | h59 | h59
          · linarith only [h0, h59, hlam, ht01, u1elo1]
          · linarith only [h0, h59, hlam, ht01, u1elo1]
          · linarith only [h0, h56, h59, hlam, ht01, u1elo1]
          · linarith only [h0, h57, h59, hlam, ht01, u1elo1]
          · linarith only [h0, h58, h59, hlam, ht01, u1elo1]
        · rcases h0emin with h65 | h65 | h65 | h65 | h65
          · linarith only [h0, h65, hlam, ht01, u1elo1]
          · linarith only [h0, h65, hlam, ht01, u1elo1]
          · linarith only [h0, h56, h65, hlam, ht01, u1elo1]
          · linarith only [h0, h57, h65, hlam, ht01, u1elo1]
          · linarith only [h58, h65, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h71 | h71
        · rcases h0emin with h72 | h72 | h72 | h72 | h72
          · linarith only [h0, h72, hlam, ht01, u1elo1]
          · linarith only [h0, h72, hlam, ht01, u1elo1]
          · linarith only [h0, h56, h72, hlam, ht01, u1elo1]
          · linarith only [h57, h72, hlam, ht01, u1elo3]
          · linarith only [h0, h71, h72, hlam, ht01, u1elo1]
        · rcases h0emin with h78 | h78 | h78 | h78 | h78
          · linarith only [h0, h78, hlam, ht01, u1elo1]
          · linarith only [h0, h78, hlam, ht01, u1elo1]
          · linarith only [h0, h56, h78, hlam, ht01, u1elo1]
          · linarith only [h57, h78, hlam, ht01, u1elo3]
          · linarith only [h71, h78, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h84 | h84
      · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
        · rcases h0emin with h86 | h86 | h86 | h86 | h86
          · linarith only [h0, h86, hlam, ht01, u1elo1]
          · linarith only [h0, h86, hlam, ht01, u1elo1]
          · linarith only [h56, h86, hlam, ht01, u1elo2]
          · linarith only [h0, h84, h86, hlam, ht01, u1elo1]
          · linarith only [h0, h85, h86, hlam, ht01, u1elo1]
        · rcases h0emin with h92 | h92 | h92 | h92 | h92
          · linarith only [h0, h92, hlam, ht01, u1elo1]
          · linarith only [h0, h92, hlam, ht01, u1elo1]
          · linarith only [h56, h92, hlam, ht01, u1elo2]
          · linarith only [h0, h84, h92, hlam, ht01, u1elo1]
          · linarith only [h85, h92, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
        · rcases h0emin with h99 | h99 | h99 | h99 | h99
          · linarith only [h0, h99, hlam, ht01, u1elo1]
          · linarith only [h0, h99, hlam, ht01, u1elo1]
          · linarith only [h56, h99, hlam, ht01, u1elo2]
          · linarith only [h84, h99, hlam, ht01, u1elo3]
          · linarith only [h0, h98, h99, hlam, ht01, u1elo1]
        · rcases h0emin with h105 | h105 | h105 | h105 | h105
          · linarith only [h0, h105, hlam, ht01, u1elo1]
          · linarith only [h0, h105, hlam, ht01, u1elo1]
          · linarith only [h105, h56, hlam, ht01, u1elo2]
          · linarith only [h105, h84, hlam, ht01, u1elo3]
          · linarith only [h105, h98, hlam, ht01, u1elo4]

theorem r1l7_20_12_13_15_M_IR_L_I_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
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
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h5, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h5, h7, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · rcases h0bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc01, hlam, hphi, p17_1, u0ehi1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc01, hlam, hphi, p17_1, u0ehi2]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc01, hlam, hphi, p17_1, u0ehi3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc01, hlam, hphi, p17_1, u0ehi4]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h0, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h3, h6, hc02, hlam, hphi, ht0b, ht5b, p17_1, u5ehi3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, p17_1, u0ehi3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, p17_1, u0ehi4]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h1, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h3, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc03, hlam, hphi, p17_1, u0ehi3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, hphi, ht01, ht12, ht23, p17_1, u0ehi4, u3elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc04, hlam, hphi, p17_1, u0ehi0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h3, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17_1, u3elo0, u5ehi3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h4, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h4, hlam, hphi, ht01, ht12, ht23, p17_1, u0ehi4, u3elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h3, h6, hc05, hlam, hphi, ht0b, ht5b, p17_1, u5ehi3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h5, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h5, hlam, hphi, ht01, ht12, ht23, p17_1, u0ehi3, u3elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                    · linarith only [h14, h16, h6, hlam]
                  · linarith only [h14, h15, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h14, h5, hc13, hlam, hphi, u3elo0]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
          · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
            · linarith only [h0, h2, h49, h51, hlam]
            · linarith only [h51, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
          · linarith only [h50, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h49, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h57 | h57
    · rcases m.htr 0 1 5 (by decide) (by decide) with h58 | h58
      · rcases m.htr 0 2 3 (by decide) (by decide) with h59 | h59
        · rcases m.htr 0 3 4 (by decide) (by decide) with h60 | h60
          · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
            · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
              · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h57, h63, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · linarith only [h61, h62, h63, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h58, h62, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h60, h61, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
          · linarith only [h60, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h0, h58, h59, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h70 | h70
        · rcases m.htr 0 3 4 (by decide) (by decide) with h71 | h71
          · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
            · linarith only [h57, h58, h72, hlam]
            · linarith only [h71, h72, hlam, hphi, ht01, ht12, ht23, u0ehi3, u3elo4]
          · linarith only [h71, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · linarith only [h0, h57, h70, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
    · linarith only [h57, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_12_13_15_M_LI_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
              · linarith only [h1, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
              · linarith only [h1, h3, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
              · linarith only [h1, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
              · linarith only [h1, h10, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
          · linarith only [h0, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
            · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
              · linarith only [h1, h16, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, h3, hc34, hlam, hphi, u3ehi4]
                · linarith only [h18, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
              · linarith only [h1, h21, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                · linarith only [h1, h23, h3, hc34, hlam, hphi, u3ehi4]
                · linarith only [h23, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h27 | h27
      · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · linarith only [h0, h29, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h0, h1, h29, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
          · linarith only [h0, h32, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h0, h1, h32, hc12, hlam, hphi, u2elo2]
      · linarith only [h0, h27, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h36 | h36
    · linarith only [h0, h36, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
      · rcases m.htr 0 3 4 (by decide) (by decide) with h39 | h39
        · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
            · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
                · linarith only [h36, h38, h40, h43, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                · linarith only [h36, h43, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h36, h39, h42, hlam]
            · linarith only [h36, h39, h40, h41, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
          · linarith only [h0, h40, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
          · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
              · linarith only [h39, h49, h51, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                · linarith only [h51, h53, hc34, hlam, hphi, u3ehi4]
                · linarith only [h53, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · linarith only [h0, h50, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h38, h49, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
        · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
          · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
            · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
              · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                  · linarith only [h59, h63, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                  · linarith only [h58, h63, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                · linarith only [h36, h62, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
              · linarith only [h36, h58, h61, hlam]
            · linarith only [h0, h60, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h59, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
              · linarith only [h58, h70, h72, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                · linarith only [h72, h74, hc34, hlam, hphi, u3ehi4]
                · linarith only [h74, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · linarith only [h0, h71, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h70, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_M_LR_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h5, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h2, h3, h7, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · linarith only [h0, h5, h6, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h14, h5, h6, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                    · rcases h3bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        rcases p17_3 (m.d 0 3) (by simp) with h19 | h19
                        · rcases p17_3 (m.d 1 3) (by simp) with h20 | h20
                          · linarith only [h1, h20, hlam]
                          · rcases p17_3 (m.d 2 3) (by simp) with h22 | h22
                            · linarith only [h2, h22, hlam]
                            · rcases p17_3 (m.d 3 4) (by simp) with h24 | h24
                              · linarith only [h24, h3, hlam]
                              · linarith only [h16, h24, h6, hlam]
                        · linarith only [h1, h19, hlam]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        rcases p17_3 (m.d 0 3) (by simp) with h28 | h28
                        · rcases p17_3 (m.d 1 3) (by simp) with h29 | h29
                          · linarith only [h1, h29, hlam]
                          · linarith only [h29, h5, hlam]
                        · linarith only [h2, h28, hlam]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, h2, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p17_1, u2elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p17_1, u2elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h1, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, h6, hc23, hc34, hlam, hphi, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, h6, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h6, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h5, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h12, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h3, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p17_1, u2elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p17_1, u2elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, h3, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p17_1, u2elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h4, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h5, hc23, hlam, hphi, ht34, ht45, p17_1, u5elo3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p17_1, u2elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                    · linarith only [h12, h16, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
          · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
            · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
              · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                · linarith only [h3, h58, h59, h61, hc12, hlam, hphi, ht01, u0ehi9]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h0, h59, h63, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h1, h60, h63, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h3, h58, h60, hc13, hc34, hlam, hphi]
            · linarith only [h2, h59, hc12, hlam, hphi, u2elo0]
          · linarith only [h58, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h70 | h70
      · linarith only [h0, h1, h70, hlam]
      · linarith only [h70, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_13_15_M_LR_L_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h2, h6, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h4, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h2, h9, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h1, h12, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h1, h14, h17, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h1, h14, h16, h17, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h12, h16, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h12, h14, h15, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h14, h2, h4, hc13, hlam, hphi, u3elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
    · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
      · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h26, h31, h34, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h26, h31, h33, h34, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h27, h33, h37, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases h2bigk with h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h0, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h32, hc35, hlam, hphi, ht0b, ht5b, p39_1, u0elo1]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        rcases p39_3 (m.d 0 2) (by simp) with h43 | h43
                        · rcases p39_3 (m.d 1 2) (by simp) with h44 | h44
                          · rcases p39_3 (m.d 2 3) (by simp) with h45 | h45
                            · linarith only [h26, h45, hlam]
                            · linarith only [h31, h45, hlam]
                          · linarith only [h30, h44, hlam]
                        · linarith only [h43, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        rcases p39_3 (m.d 0 2) (by simp) with h50 | h50
                        · rcases p39_3 (m.d 1 2) (by simp) with h51 | h51
                          · rcases p39_3 (m.d 2 3) (by simp) with h52 | h52
                            · linarith only [h26, h52, hlam]
                            · linarith only [h32, h52, hlam]
                          · linarith only [h0, h51, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]
                        · linarith only [h50, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hc12, hlam, hphi, ht01, p39_1, u0ehi6]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        rcases p39_3 (m.d 0 2) (by simp) with h59 | h59
                        · linarith only [h0, h59, hlam]
                        · linarith only [h26, h59, hlam]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        rcases p39_3 (m.d 0 2) (by simp) with h62 | h62
                        · linarith only [h0, h62, hlam]
                        · linarith only [h26, h32, h33, h37, h62, hc34, hc45, hlam, hphi]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        rcases p39_3 (m.d 0 2) (by simp) with h65 | h65
                        · linarith only [h0, h65, hlam]
                        · linarith only [h26, h32, h65, hlam]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h26, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h29, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h26, hc24, hlam, hphi, ht0b, ht45, ht5b, p39_1, u0elo1]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h26, hc25, hlam, hphi, ht0b, ht5b, p39_1, u0elo1]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h30, hc14, hlam, hphi, ht01, p39_1, u0ehi6]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h30, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h31, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h33, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht12, p39_1, u0ehi6]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h26, h32, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p39_1, u0elo1]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h32, hlam, p39_0]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [h26, h32, hc24, hlam, hphi, ht0b, ht45, ht5b, p39_1, u0elo1]
                      · have p39_0 := h39c.1
                        have p39_1 := h39c.2.1
                        have p39_2 := h39c.2.2.1
                        have p39_3 := h39c.2.2.2
                        linarith only [hlam, p39_0]
                · linarith only [h28, h32, hc23, hlam, hphi, u3elo0]
              · linarith only [h27, h31, hc23, hlam, hphi, u3elo0]
            · linarith only [h0, h30, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h29, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h28, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
      · linarith only [h27, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
    · linarith only [h26, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]

theorem r1l7_20_12_13_15_M_LR_L_R_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
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
                        linarith only [h3, h6, hlam, hphi, ht23, p10_1, u2ehi4, u3elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, hphi, ht23, p10_1, u2ehi4, u3elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        rcases p10_3 (m.d 0 5) (by simp) with h14 | h14
                        · rcases p10_3 (m.d 1 5) (by simp) with h15 | h15
                          · linarith only [h1, h15, hlam]
                          · linarith only [h15, h7, hlam]
                        · linarith only [h14, h3, hlam]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        rcases p10_3 (m.d 0 5) (by simp) with h19 | h19
                        · rcases p10_3 (m.d 1 5) (by simp) with h20 | h20
                          · linarith only [h1, h20, hlam]
                          · linarith only [h20, h3, h6, hlam, hphi, ht23, p10_1, u2ehi4, u3elo0]
                        · linarith only [h19, h4, hlam]
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
                        linarith only [h0, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10_1, u0elo0, u2ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h7, hc35, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h7, hc45, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hlam, p10_1]
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
                        linarith only [h2, hc35, hlam, hphi, ht0b, ht5b, p10_1, u0elo1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h6, h7, hc45, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h8, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h6, hc45, hlam, hphi, ht23, ht34, p10_1, u2ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h6, h7, h9, hc35, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                    · linarith only [h4, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                  · linarith only [h8, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h3, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h2, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
              · linarith only [h48, h5, hc24, hlam, hphi, u2ehi4]
              · linarith only [h2, h48, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h4, h51, h55, hc12, hlam, hphi, ht01, u0ehi8]
                    · rcases h5bigk with h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h3, h52, h55, hlam, hphi, ht23, p57_1, u2ehi3, u3elo0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h3, h55, hlam, hphi, ht23, p57_1, u2ehi3, u3elo0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        rcases p57_3 (m.d 0 5) (by simp) with h61 | h61
                        · rcases p57_3 (m.d 1 5) (by simp) with h62 | h62
                          · linarith only [h1, h62, hlam]
                          · linarith only [h53, h62, hlam]
                        · linarith only [h3, h61, hlam]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h4, hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h1, hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h1, h55, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p57_1, u0elo0, u2ehi3]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h0, h53, hc35, hlam, hphi, ht0b, ht5b, p57_1, u0elo0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h0, h53, hc45, hlam, hphi, ht0b, ht5b, p57_1, u0elo0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h2, hlam, p57_1]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h52, hlam, p57_1]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht0b, ht5b, p57_1, u0elo1]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h55, hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h3, hlam, p57_1]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h53, hlam, p57_1]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h54, hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [hlam, p57_0]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h4, hlam, hphi, ht01, ht12, ht23, p57_1, u0ehi8, u3elo4]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h0, h52, h53, hc45, hlam, hphi, ht23, ht34, p57_1, u0ehi9, u0elo0, u2ehi4]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h52, h55, hc45, hlam, hphi, ht23, ht34, p57_1, u2ehi3]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [h55, hc45, hlam, hphi, ht23, ht34, p57_1, u2ehi3]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        rcases p57_3 (m.d 0 5) (by simp) with h85 | h85
                        · linarith only [h4, h85, hlam]
                        · linarith only [h3, h85, hlam]
                      · have p57_0 := h57c.1
                        have p57_1 := h57c.2.1
                        have p57_2 := h57c.2.2.1
                        have p57_3 := h57c.2.2.2
                        linarith only [hlam, p57_0]
                  · linarith only [h0, h53, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h3, h53, hc13, hlam, hphi, u3elo0]
              · linarith only [h2, h52, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
              · linarith only [h51, h92, hc24, hlam, hphi, u2ehi4]
              · linarith only [h2, h92, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
        · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
          · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
            · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
              · linarith only [h2, h99, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h98, h99, hc25, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
              · linarith only [h102, h98, hc24, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h102, h104, h105, h2, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1, u3elo2]
                  · linarith only [h105, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h104, h96, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
            · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
              · linarith only [h110, h2, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h109, h110, hc25, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
              · linarith only [h109, h113, hc24, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                  · linarith only [h0, h113, h115, h116, h2, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1, u3elo2]
                  · linarith only [h116, hlam, hphi, ht23, u2ehi2, u3elo4]
                · linarith only [h115, h96, hc13, hlam, hphi, u3elo0]
        · linarith only [h96, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
      · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
        · linarith only [h0, h1, h122, hlam]
        · linarith only [h122, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
        · linarith only [h0, h1, h125, hlam]
        · linarith only [h125, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem r1l7_20_12_13_15_M_LR_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h0, h2, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h0, h2, h3, h4, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
            · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
          · linarith only [h1, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h15, h3, hc14, hlam, hphi, ht01, u0ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h0, h17, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
            · linarith only [h0, h14, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
          · linarith only [h1, h13, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
            · linarith only [h2, h24, hc13, hlam, hphi, ht01, u0ehi7]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
              · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                · linarith only [h2, h27, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h1, h29, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                  · linarith only [h22, h27, h29, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
              · linarith only [h1, h22, h23, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
          · linarith only [h1, h23, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
          · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
            · linarith only [h2, h35, hc13, hlam, hphi, ht01, u0ehi7]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
              · linarith only [h22, h37, hc14, hlam, hphi, ht01, u0ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                · linarith only [h2, h39, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h1, h37, h41, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h2, h22, h43, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                    · linarith only [h2, h43, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
          · linarith only [h1, h34, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h48 | h48
    · linarith only [h0, h48, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
      · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
        · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
          · linarith only [h48, h52, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
            · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
              · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h50, h58, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                    · linarith only [h51, h58, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                  · linarith only [h48, h55, h57, hc14, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h56, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · linarith only [h50, h51, h52, h55, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
            · linarith only [h50, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
          · linarith only [h48, h65, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
            · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
              · linarith only [h51, h68, hc14, hlam, hphi, ht01, u0ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h48, h51, h70, h71, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · linarith only [h48, h71, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                · linarith only [h0, h67, h70, hc13, hlam, hphi, ht01, u0ehi6]
            · linarith only [h50, h67, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
        · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
          · linarith only [h48, h77, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
            · linarith only [h50, h79, hc13, hlam, hphi, ht01, u0ehi7]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
              · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                · linarith only [h0, h50, h82, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · linarith only [h0, h82, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · linarith only [h76, h79, h81, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
          · linarith only [h48, h86, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
            · linarith only [h0, h50, h88, hc13, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
              · linarith only [h0, h50, h76, h90, hc14, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                · linarith only [h0, h50, h92, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · linarith only [h0, h92, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

theorem r1l7_20_12_13_M_IR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                            · linarith only [h13, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                          · linarith only [h11, h12, h3, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                        · linarith only [h11, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                      · linarith only [h10, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h23, h8, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                            · linarith only [h25, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                            · linarith only [h25, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                        · linarith only [h22, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                      · linarith only [h21, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h20, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32 | h32
                · linarith only [h32, h6, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                        · linarith only [h37, h6, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                            · linarith only [h40, h6, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                              · linarith only [h0, h32, h35, h42, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                                · rcases h0bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h0, h36, h42, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p45_1, u3ehi2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hc01, hlam, hphi, p45_1, u0ehi2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, h34, hc01, hlam, hphi, p45_1, u0ehi2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, hc01, hlam, hphi, p45_1, u0ehi2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h0, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht12, p45_1, u0ehi2, u2elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, h34, hlam, hphi, ht01, ht12, p45_1, u0ehi2, u2elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, hlam, hphi, ht01, ht12, p45_1, u0ehi2, u2elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, h44, hc01, hc34, hlam, hphi, ht12, ht23, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h3, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h6, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h1, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h4, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hc04, hlam, hphi, p45_1, u0ehi2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h32, h4, hlam, hphi, ht01, ht12, p45_1, u0ehi2, u2elo0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h2, hlam, p45_1]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h5, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hc05, hlam, hphi, p45_1, u0ehi2]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [h34, hlam, p45_0]
                                  · have p45_0 := h45c.1
                                    have p45_1 := h45c.2.1
                                    have p45_2 := h45c.2.2.1
                                    have p45_3 := h45c.2.2.2
                                    linarith only [hlam, p45_0]
                                · linarith only [h1, h37, h39, h4, h44, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                          · linarith only [h34, h35, h37, h39, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                      · linarith only [h36, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h3, h35, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                        · linarith only [h6, h77, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                          · linarith only [h34, h79, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h6, h75, h81, hc12, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h0, h75, h83, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h34, h6, h85, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                · linarith only [h0, h6, h76, h83, h85, hc45, hlam, hphi, ht01, ht12, ht34, u0ehi2, u2elo0, u3ehi2]
                      · linarith only [h5, h76, hc12, hlam, hphi, u2elo0]
                    · linarith only [h3, h75, hc12, hlam, hphi, u2elo0]
            · linarith only [h3, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
          · linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h93 | h93
        · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
          · rcases m.htr 0 2 5 (by decide) (by decide) with h95 | h95
            · linarith only [h0, h2, h95, hlam]
            · linarith only [h95, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
          · linarith only [h93, h94, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · linarith only [h93, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h100 | h100
      · rcases m.htr 0 2 3 (by decide) (by decide) with h101 | h101
        · rcases m.htr 0 2 4 (by decide) (by decide) with h102 | h102
          · linarith only [h0, h1, h102, hlam]
          · linarith only [h102, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
        · linarith only [h101, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h106 | h106
        · rcases m.htr 0 2 4 (by decide) (by decide) with h107 | h107
          · linarith only [h0, h1, h107, hlam]
          · linarith only [h107, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
        · linarith only [h106, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

end R2N4
