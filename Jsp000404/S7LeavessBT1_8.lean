import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT1_H_I_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
    · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
          · linarith only [h0, h30, hlam, ht01, u1elo0]
          · linarith only [h0, h30, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
          · linarith only [h0, h29, h33, hlam, ht01, u1elo3]
          · linarith only [h0, h33, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
          · linarith only [h0, h28, h37, hlam, ht01, u1elo2]
          · linarith only [h0, h37, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
          · linarith only [h0, h28, h40, hlam, ht01, u1elo2]
          · linarith only [h0, h40, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h27, h45, hlam, ht01, u1elo1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
          · linarith only [h0, h27, h48, hlam, ht01, u1elo1]
          · linarith only [h0, h48, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
        · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
          · linarith only [h0, h27, h52, hlam, ht01, u1elo1]
          · linarith only [h0, h52, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
          · linarith only [h0, h27, h55, hlam, ht01, u1elo1]
          · linarith only [h0, h55, hlam, ht01, u1elo4]

theorem n7l_sBT1_H_I_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h5elo := hb5.1
  have h1elo := hb1.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · linarith only [h0, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]

theorem n7l_sBT1_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem n7l_sBT1_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
        · linarith only [h14, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h16 | h16
          · rcases m.htr 0 2 5 (by decide) (by decide) with h17 | h17
            · linarith only [h12, h14, h17, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h12, h14, h20, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h12, h14, h16, h20, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
              · linarith only [h0, h19, hc45, hlam, ht01, ht12, ht23, ht34]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h24 | h24
            · linarith only [h13, h14, h16, h24, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                · linarith only [h12, h14, h16, h27, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h29, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                  · linarith only [h14, h26, h29, hlam]
              · linarith only [h0, h26, hc45, hlam, ht01, ht12, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
        · linarith only [h13, h33, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h35 | h35
          · linarith only [h12, h13, h35, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h37 | h37
            · linarith only [h12, h13, h37, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                · linarith only [h12, h13, h35, h40, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h42, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                  · linarith only [h33, h39, h42, hlam]
              · linarith only [h0, h39, hc45, hlam, ht01, ht12, ht23, ht34]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h46 | h46
      · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
        · linarith only [h12, h47, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h49 | h49
          · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
            · linarith only [h12, h50, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                  · linarith only [h54, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                  · linarith only [h47, h52, h54, hlam]
                · linarith only [h12, h47, h49, h50, h53, hc01, hlam, hphi, u1elo4]
              · linarith only [h0, h52, hc45, hlam, ht01, ht12, ht23, ht34]
          · linarith only [h12, h46, h49, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h60 | h60
        · linarith only [h12, h60, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h62 | h62
          · rcases m.htr 0 2 5 (by decide) (by decide) with h63 | h63
            · linarith only [h12, h63, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
              · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                  · linarith only [h67, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                  · linarith only [h60, h65, h67, hlam]
                · linarith only [h62, h63, h66, hc12, hc25, hlam, hphi]
              · linarith only [h0, h65, hc45, hlam, ht01, ht12, ht23, ht34]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h72 | h72
            · linarith only [h12, h72, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                · linarith only [h12, h62, h75, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h77, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                  · linarith only [h60, h74, h77, hlam]
              · linarith only [h0, h74, hc45, hlam, ht01, ht12, ht23, ht34]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h81 | h81
    · rcases m.htr 0 1 3 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 1 5 (by decide) (by decide) with h83 | h83
        · linarith only [h83, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
        · linarith only [h0, h83, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h86 | h86
        · linarith only [h82, h86, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · linarith only [h0, h86, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h89 | h89
      · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
        · linarith only [h81, h90, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · linarith only [h0, h90, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h93 | h93
        · linarith only [h81, h93, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · linarith only [h0, h93, hlam, ht01, u1elo4]

theorem n7l_sBT1_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
              · linarith only [h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
            · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
              · linarith only [h13, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h13, hlam, p0_0]
            · linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · linarith only [h19, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h19, hlam, p0_0]
            · linarith only [h18, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · linarith only [h24, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h24, hlam, p0_0]
            · linarith only [h23, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · rcases p0_3 (m.d 0 2) (by simp) with h30 | h30
      · rcases p0_3 (m.d 0 3) (by simp) with h31 | h31
        · linarith only [h31, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h33 | h33
          · rcases p0_3 (m.d 0 5) (by simp) with h34 | h34
            · rcases m.htr 0 1 2 (by decide) (by decide) with h35 | h35
              · linarith only [h30, h35, hlam]
              · linarith only [h35, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h34, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h39 | h39
            · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
              · linarith only [h30, h40, hlam]
              · linarith only [h40, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h39, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h44 | h44
        · linarith only [h44, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h46 | h46
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
              · linarith only [h30, h48, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h30, h48, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h47, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h52 | h52
            · rcases m.htr 0 1 2 (by decide) (by decide) with h53 | h53
              · linarith only [h30, h53, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h30, h53, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h52, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h29, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h58 | h58
    · rcases p0_3 (m.d 0 2) (by simp) with h59 | h59
      · rcases p0_3 (m.d 0 3) (by simp) with h60 | h60
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · rcases m.htr 0 1 2 (by decide) (by decide) with h64 | h64
              · linarith only [h59, h64, hlam]
              · linarith only [h64, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h63, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
          · linarith only [h68, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · linarith only [h59, h71, hlam]
              · linarith only [h60, h71, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h70, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h75 | h75
        · rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
          · linarith only [h76, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h78 | h78
            · rcases m.htr 0 1 2 (by decide) (by decide) with h79 | h79
              · linarith only [h59, h79, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h59, h79, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h78, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h85 | h85
            · rcases m.htr 0 1 2 (by decide) (by decide) with h86 | h86
              · linarith only [h59, h86, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h59, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h85, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h58, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h94 | h94
    · rcases p0_3 (m.d 0 2) (by simp) with h95 | h95
      · rcases p0_3 (m.d 0 3) (by simp) with h96 | h96
        · linarith only [h96, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h98 | h98
          · rcases p0_3 (m.d 0 5) (by simp) with h99 | h99
            · rcases m.htr 0 1 2 (by decide) (by decide) with h100 | h100
              · rcases m.htr 0 1 3 (by decide) (by decide) with h101 | h101
                · linarith only [h100, h101, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h100, h101, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h100, h94, hlam]
            · linarith only [h99, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h106 | h106
            · rcases m.htr 0 1 2 (by decide) (by decide) with h107 | h107
              · rcases m.htr 0 1 3 (by decide) (by decide) with h108 | h108
                · linarith only [h107, h108, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h107, h108, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h107, h94, hlam]
            · linarith only [h106, h94, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h95, hlam, p0_0]
    · linarith only [h94, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h115 | h115
    · rcases p0_3 (m.d 0 2) (by simp) with h116 | h116
      · rcases p0_3 (m.d 0 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
          · linarith only [h118, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h120 | h120
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 4 (by decide) (by decide) with h123 | h123
                  · linarith only [h121, h123, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h121, h123, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h121, h122, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h115, h121, hlam]
            · linarith only [h120, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h129 | h129
          · linarith only [h129, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h131 | h131
            · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
              · rcases m.htr 0 1 3 (by decide) (by decide) with h133 | h133
                · linarith only [h117, h132, h133, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h117, h132, h133, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h115, h132, hlam]
            · linarith only [h115, h131, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h116, hlam, p0_0]
    · linarith only [h115, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h142 | h142
    · rcases p0_3 (m.d 0 2) (by simp) with h143 | h143
      · linarith only [h143, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h145 | h145
        · rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
              · linarith only [h148, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h142, h148, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h142, h147, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h152 | h152
            · rcases m.htr 0 1 2 (by decide) (by decide) with h153 | h153
              · linarith only [h142, h153, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h142, h153, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h142, h152, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h145, hlam, p0_0]
    · linarith only [h142, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · rcases p0_3 (m.d 0 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
          · linarith only [h163, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
            · rcases m.htr 0 1 2 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 1 3 (by decide) (by decide) with h167 | h167
                · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
                  · linarith only [h161, h166, h168, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h161, h166, h168, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h160, h167, hlam]
              · linarith only [h160, h166, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h160, h165, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h162, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h175 | h175
        · rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
          · linarith only [h176, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h178 | h178
            · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
              · linarith only [h160, h161, h179, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h160, h161, h179, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h160, h178, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h175, hlam, p0_0]
    · linarith only [h160, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h187 | h187
    · rcases p0_3 (m.d 0 2) (by simp) with h188 | h188
      · linarith only [h188, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h190 | h190
        · rcases p0_3 (m.d 0 4) (by simp) with h191 | h191
          · rcases p0_3 (m.d 0 5) (by simp) with h192 | h192
            · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
              · linarith only [h193, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h187, h193, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h187, h192, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h191, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h198 | h198
          · rcases p0_3 (m.d 0 5) (by simp) with h199 | h199
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h187, h200, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h187, h200, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h187, h199, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h198, hlam, p0_0]
    · linarith only [h187, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h206 | h206
    · rcases p0_3 (m.d 0 2) (by simp) with h207 | h207
      · rcases p0_3 (m.d 0 3) (by simp) with h208 | h208
        · linarith only [h208, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 0 5) (by simp) with h211 | h211
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · linarith only [h207, h212, h213, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h207, h212, h213, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h206, h212, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h206, h211, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h210, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h219 | h219
        · linarith only [h219, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h221 | h221
          · rcases p0_3 (m.d 0 5) (by simp) with h222 | h222
            · rcases m.htr 0 1 2 (by decide) (by decide) with h223 | h223
              · linarith only [h206, h207, h223, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h206, h207, h223, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h206, h222, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h221, hlam, p0_0]
    · linarith only [h206, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h232 | h232
    · rcases p0_3 (m.d 0 2) (by simp) with h233 | h233
      · linarith only [h233, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h235 | h235
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 0 5) (by simp) with h237 | h237
            · rcases m.htr 0 1 2 (by decide) (by decide) with h238 | h238
              · linarith only [h238, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h238, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h237, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h242 | h242
            · rcases m.htr 0 1 2 (by decide) (by decide) with h243 | h243
              · linarith only [h232, h243, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h243, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h242, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h247 | h247
          · rcases p0_3 (m.d 0 5) (by simp) with h248 | h248
            · rcases m.htr 0 1 2 (by decide) (by decide) with h249 | h249
              · linarith only [h247, h249, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h249, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h248, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h253 | h253
            · rcases m.htr 0 1 2 (by decide) (by decide) with h254 | h254
              · linarith only [h232, h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h254, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h253, hlam, p0_0]
    · linarith only [h232, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h259 | h259
    · rcases p0_3 (m.d 0 2) (by simp) with h260 | h260
      · rcases p0_3 (m.d 0 3) (by simp) with h261 | h261
        · linarith only [h261, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · rcases m.htr 0 1 2 (by decide) (by decide) with h265 | h265
              · rcases m.htr 0 1 3 (by decide) (by decide) with h266 | h266
                · linarith only [h260, h265, h266, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h260, h265, h266, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h259, h265, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 1 3 (by decide) (by decide) with h273 | h273
                · linarith only [h260, h272, h273, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h260, h272, h273, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h259, h272, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h271, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h278 | h278
        · linarith only [h278, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 0 5) (by simp) with h281 | h281
            · rcases m.htr 0 1 2 (by decide) (by decide) with h282 | h282
              · linarith only [h260, h280, h282, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h259, h260, h282, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h281, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h286 | h286
            · rcases m.htr 0 1 2 (by decide) (by decide) with h287 | h287
              · linarith only [h260, h287, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h259, h260, h287, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h286, hlam, p0_0]
    · linarith only [h259, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h292 | h292
    · rcases p0_3 (m.d 0 2) (by simp) with h293 | h293
      · rcases p0_3 (m.d 0 3) (by simp) with h294 | h294
        · rcases p0_3 (m.d 0 4) (by simp) with h295 | h295
          · linarith only [h295, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h297 | h297
            · rcases m.htr 0 1 2 (by decide) (by decide) with h298 | h298
              · rcases m.htr 0 1 3 (by decide) (by decide) with h299 | h299
                · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
                  · linarith only [h293, h298, h300, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h293, h298, h300, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h293, h298, h299, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h292, h298, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h297, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h306 | h306
          · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                · linarith only [h293, h294, h309, h310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h293, h294, h309, h310, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h292, h294, h309, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h308, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h315 | h315
        · rcases p0_3 (m.d 0 4) (by simp) with h316 | h316
          · linarith only [h316, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h318 | h318
            · rcases m.htr 0 1 2 (by decide) (by decide) with h319 | h319
              · linarith only [h292, h293, h319, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h292, h293, h319, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h318, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h323 | h323
          · linarith only [h323, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h325 | h325
            · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
              · linarith only [h293, h326, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h292, h293, h326, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h325, hlam, p0_0]
    · linarith only [h292, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_H_I_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h5ehi := hb5.2.1
  have h1elo := hb1.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
    · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
          · linarith only [h0, h30, hlam, ht01, u1elo0]
          · linarith only [h0, h30, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
          · linarith only [h29, h33, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
          · linarith only [h0, h33, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
          · linarith only [h28, h37, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
          · linarith only [h0, h37, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
          · linarith only [h28, h40, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
          · linarith only [h0, h40, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h27, h45, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
          · linarith only [h27, h48, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h48, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
        · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
          · linarith only [h27, h52, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h52, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
          · linarith only [h27, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
          · linarith only [h0, h55, hlam, ht01, u1elo4]

theorem n7l_sBT1_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5ehi := hb5.2.1
  have h1ehi := hb1.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
              · linarith only [h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h8, hlam, p0_0]
            · linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
            · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
              · linarith only [h13, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h13, hlam, p0_0]
            · linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 0 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · linarith only [h19, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h19, hlam, p0_0]
            · linarith only [h18, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · linarith only [h24, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h24, hlam, p0_0]
            · linarith only [h23, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · rcases p0_3 (m.d 0 2) (by simp) with h30 | h30
      · rcases p0_3 (m.d 0 3) (by simp) with h31 | h31
        · linarith only [h31, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h33 | h33
          · rcases p0_3 (m.d 0 5) (by simp) with h34 | h34
            · rcases m.htr 0 1 2 (by decide) (by decide) with h35 | h35
              · linarith only [h30, h35, hlam]
              · linarith only [h35, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h34, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h39 | h39
            · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
              · linarith only [h30, h40, hlam]
              · linarith only [h40, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h39, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h44 | h44
        · linarith only [h44, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h46 | h46
          · rcases p0_3 (m.d 0 5) (by simp) with h47 | h47
            · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
              · linarith only [h30, h48, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h30, h48, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h47, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h52 | h52
            · rcases m.htr 0 1 2 (by decide) (by decide) with h53 | h53
              · linarith only [h30, h53, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h30, h53, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h52, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h29, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h58 | h58
    · rcases p0_3 (m.d 0 2) (by simp) with h59 | h59
      · rcases p0_3 (m.d 0 3) (by simp) with h60 | h60
        · rcases p0_3 (m.d 0 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h63 | h63
            · rcases m.htr 0 1 2 (by decide) (by decide) with h64 | h64
              · linarith only [h59, h64, hlam]
              · linarith only [h64, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h63, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
          · linarith only [h68, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h70 | h70
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · linarith only [h59, h71, hlam]
              · linarith only [h60, h71, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h70, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · rcases p0_3 (m.d 0 3) (by simp) with h75 | h75
        · rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
          · linarith only [h76, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h78 | h78
            · rcases m.htr 0 1 2 (by decide) (by decide) with h79 | h79
              · linarith only [h59, h79, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h59, h79, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h78, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h85 | h85
            · rcases m.htr 0 1 2 (by decide) (by decide) with h86 | h86
              · linarith only [h59, h86, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h59, h86, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h85, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
    · linarith only [h58, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h94 | h94
    · rcases p0_3 (m.d 0 2) (by simp) with h95 | h95
      · rcases p0_3 (m.d 0 3) (by simp) with h96 | h96
        · linarith only [h96, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h98 | h98
          · rcases p0_3 (m.d 0 5) (by simp) with h99 | h99
            · rcases m.htr 0 1 2 (by decide) (by decide) with h100 | h100
              · rcases m.htr 0 1 3 (by decide) (by decide) with h101 | h101
                · linarith only [h100, h101, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h100, h101, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h100, h94, hlam]
            · linarith only [h99, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h106 | h106
            · rcases m.htr 0 1 2 (by decide) (by decide) with h107 | h107
              · rcases m.htr 0 1 3 (by decide) (by decide) with h108 | h108
                · linarith only [h107, h108, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h107, h108, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h107, h94, hlam]
            · linarith only [h106, h94, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h95, hlam, p0_0]
    · linarith only [h94, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h115 | h115
    · rcases p0_3 (m.d 0 2) (by simp) with h116 | h116
      · rcases p0_3 (m.d 0 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
          · linarith only [h118, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h120 | h120
            · rcases m.htr 0 1 2 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 1 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 1 4 (by decide) (by decide) with h123 | h123
                  · linarith only [h121, h123, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h121, h123, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h121, h122, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h115, h121, hlam]
            · linarith only [h120, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · rcases p0_3 (m.d 0 4) (by simp) with h129 | h129
          · linarith only [h129, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h131 | h131
            · rcases m.htr 0 1 2 (by decide) (by decide) with h132 | h132
              · rcases m.htr 0 1 3 (by decide) (by decide) with h133 | h133
                · linarith only [h117, h132, h133, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h117, h132, h133, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h115, h132, hlam]
            · linarith only [h115, h131, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
      · linarith only [h116, hlam, p0_0]
    · linarith only [h115, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h142 | h142
    · rcases p0_3 (m.d 0 2) (by simp) with h143 | h143
      · linarith only [h143, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h145 | h145
        · rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
              · linarith only [h148, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h142, h148, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h142, h147, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · rcases p0_3 (m.d 0 5) (by simp) with h152 | h152
            · rcases m.htr 0 1 2 (by decide) (by decide) with h153 | h153
              · linarith only [h142, h153, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h142, h153, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h142, h152, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h145, hlam, p0_0]
    · linarith only [h142, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h160 | h160
    · rcases p0_3 (m.d 0 2) (by simp) with h161 | h161
      · rcases p0_3 (m.d 0 3) (by simp) with h162 | h162
        · rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
          · linarith only [h163, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h165 | h165
            · rcases m.htr 0 1 2 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 1 3 (by decide) (by decide) with h167 | h167
                · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
                  · linarith only [h161, h166, h168, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h161, h166, h168, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h160, h167, hlam]
              · linarith only [h160, h166, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h160, h165, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h162, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h175 | h175
        · rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
          · linarith only [h176, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h178 | h178
            · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
              · linarith only [h160, h161, h179, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h160, h161, h179, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h160, h178, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
        · linarith only [h175, hlam, p0_0]
    · linarith only [h160, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h187 | h187
    · rcases p0_3 (m.d 0 2) (by simp) with h188 | h188
      · linarith only [h188, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h190 | h190
        · rcases p0_3 (m.d 0 4) (by simp) with h191 | h191
          · rcases p0_3 (m.d 0 5) (by simp) with h192 | h192
            · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
              · linarith only [h193, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h187, h193, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h187, h192, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h191, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h198 | h198
          · rcases p0_3 (m.d 0 5) (by simp) with h199 | h199
            · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
              · linarith only [h187, h200, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h187, h200, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h187, h199, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h198, hlam, p0_0]
    · linarith only [h187, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h206 | h206
    · rcases p0_3 (m.d 0 2) (by simp) with h207 | h207
      · rcases p0_3 (m.d 0 3) (by simp) with h208 | h208
        · linarith only [h208, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 0 5) (by simp) with h211 | h211
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 1 3 (by decide) (by decide) with h213 | h213
                · linarith only [h207, h212, h213, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h207, h212, h213, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h206, h212, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h206, h211, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h210, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h219 | h219
        · linarith only [h219, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h221 | h221
          · rcases p0_3 (m.d 0 5) (by simp) with h222 | h222
            · rcases m.htr 0 1 2 (by decide) (by decide) with h223 | h223
              · linarith only [h206, h207, h223, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h206, h207, h223, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h206, h222, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi0]
          · linarith only [h221, hlam, p0_0]
    · linarith only [h206, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h232 | h232
    · rcases p0_3 (m.d 0 2) (by simp) with h233 | h233
      · linarith only [h233, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h235 | h235
        · rcases p0_3 (m.d 0 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 0 5) (by simp) with h237 | h237
            · rcases m.htr 0 1 2 (by decide) (by decide) with h238 | h238
              · linarith only [h238, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h238, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h237, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h242 | h242
            · rcases m.htr 0 1 2 (by decide) (by decide) with h243 | h243
              · linarith only [h232, h243, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h243, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h242, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h247 | h247
          · rcases p0_3 (m.d 0 5) (by simp) with h248 | h248
            · rcases m.htr 0 1 2 (by decide) (by decide) with h249 | h249
              · linarith only [h247, h249, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h249, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h248, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h253 | h253
            · rcases m.htr 0 1 2 (by decide) (by decide) with h254 | h254
              · linarith only [h232, h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h232, h254, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h253, hlam, p0_0]
    · linarith only [h232, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h259 | h259
    · rcases p0_3 (m.d 0 2) (by simp) with h260 | h260
      · rcases p0_3 (m.d 0 3) (by simp) with h261 | h261
        · linarith only [h261, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 0 5) (by simp) with h264 | h264
            · rcases m.htr 0 1 2 (by decide) (by decide) with h265 | h265
              · rcases m.htr 0 1 3 (by decide) (by decide) with h266 | h266
                · linarith only [h260, h265, h266, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h260, h265, h266, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h259, h265, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h271 | h271
            · rcases m.htr 0 1 2 (by decide) (by decide) with h272 | h272
              · rcases m.htr 0 1 3 (by decide) (by decide) with h273 | h273
                · linarith only [h260, h272, h273, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h260, h272, h273, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h259, h272, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h271, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h278 | h278
        · linarith only [h278, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h280 | h280
          · rcases p0_3 (m.d 0 5) (by simp) with h281 | h281
            · rcases m.htr 0 1 2 (by decide) (by decide) with h282 | h282
              · linarith only [h260, h280, h282, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h259, h260, h282, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h281, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h286 | h286
            · rcases m.htr 0 1 2 (by decide) (by decide) with h287 | h287
              · linarith only [h260, h287, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h259, h260, h287, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h286, hlam, p0_0]
    · linarith only [h259, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h292 | h292
    · rcases p0_3 (m.d 0 2) (by simp) with h293 | h293
      · rcases p0_3 (m.d 0 3) (by simp) with h294 | h294
        · rcases p0_3 (m.d 0 4) (by simp) with h295 | h295
          · linarith only [h295, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h297 | h297
            · rcases m.htr 0 1 2 (by decide) (by decide) with h298 | h298
              · rcases m.htr 0 1 3 (by decide) (by decide) with h299 | h299
                · rcases m.htr 0 1 4 (by decide) (by decide) with h300 | h300
                  · linarith only [h293, h298, h300, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
                  · linarith only [h293, h298, h300, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
                · linarith only [h293, h298, h299, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h292, h298, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h297, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h306 | h306
          · linarith only [h306, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h308 | h308
            · rcases m.htr 0 1 2 (by decide) (by decide) with h309 | h309
              · rcases m.htr 0 1 3 (by decide) (by decide) with h310 | h310
                · linarith only [h293, h294, h309, h310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi2]
                · linarith only [h293, h294, h309, h310, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h292, h294, h309, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h308, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h315 | h315
        · rcases p0_3 (m.d 0 4) (by simp) with h316 | h316
          · linarith only [h316, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h318 | h318
            · rcases m.htr 0 1 2 (by decide) (by decide) with h319 | h319
              · linarith only [h292, h293, h319, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h292, h293, h319, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h318, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h323 | h323
          · linarith only [h323, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h325 | h325
            · rcases m.htr 0 1 2 (by decide) (by decide) with h326 | h326
              · linarith only [h293, h326, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
              · linarith only [h292, h293, h326, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1]
            · linarith only [h325, hlam, p0_0]
    · linarith only [h292, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · rcases h5bigk with h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
  · rcases h5bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
  · rcases h5bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hlam, p53_0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc15, hlam, hphi, p53_1, u5elo0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc25, hlam, hphi, p53_1, u5elo0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc35, hlam, hphi, p53_1, u5elo0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc45, hlam, hphi, p53_1, u5elo0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc05, hlam, hphi, p53_1, u5elo1]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hlam, p53_0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc25, hlam, hphi, p53_1, u5elo1]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc35, hlam, hphi, p53_1, u5elo1]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc45, hlam, hphi, p53_1, u5elo1]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc05, hlam, hphi, p53_1, u5elo2]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc15, hlam, hphi, p53_1, u5elo2]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hlam, p53_0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc35, hlam, hphi, p53_1, u5elo2]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc45, hlam, hphi, p53_1, u5elo2]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc05, hlam, hphi, p53_1, u5elo3]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc15, hlam, hphi, p53_1, u5elo3]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc25, hlam, hphi, p53_1, u5elo3]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hlam, p53_0]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc45, hlam, hphi, p53_1, u5elo3]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc05, hlam, hphi, p53_1, u5elo4]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc15, hlam, hphi, p53_1, u5elo4]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc25, hlam, hphi, p53_1, u5elo4]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hc35, hlam, hphi, p53_1, u5elo4]
    · have p53_0 := h53c.1
      have p53_1 := h53c.2.1
      have p53_2 := h53c.2.2.1
      have p53_3 := h53c.2.2.2
      linarith only [hlam, p53_0]
  · rcases h5bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hlam, p79_0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc15, hlam, hphi, p79_1, u5elo0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc25, hlam, hphi, p79_1, u5elo0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc35, hlam, hphi, p79_1, u5elo0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc45, hlam, hphi, p79_1, u5elo0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc05, hlam, hphi, p79_1, u5elo1]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hlam, p79_0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc25, hlam, hphi, p79_1, u5elo1]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc35, hlam, hphi, p79_1, u5elo1]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc45, hlam, hphi, p79_1, u5elo1]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc05, hlam, hphi, p79_1, u5elo2]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc15, hlam, hphi, p79_1, u5elo2]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hlam, p79_0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc35, hlam, hphi, p79_1, u5elo2]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc45, hlam, hphi, p79_1, u5elo2]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc05, hlam, hphi, p79_1, u5elo3]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc15, hlam, hphi, p79_1, u5elo3]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc25, hlam, hphi, p79_1, u5elo3]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hlam, p79_0]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc45, hlam, hphi, p79_1, u5elo3]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc05, hlam, hphi, p79_1, u5elo4]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc15, hlam, hphi, p79_1, u5elo4]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc25, hlam, hphi, p79_1, u5elo4]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hc35, hlam, hphi, p79_1, u5elo4]
    · have p79_0 := h79c.1
      have p79_1 := h79c.2.1
      have p79_2 := h79c.2.2.1
      have p79_3 := h79c.2.2.2
      linarith only [hlam, p79_0]
  · linarith only [h0, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]

theorem n7l_sBT1_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h1ehi := hb1.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo3]
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo4]
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

theorem n7l_sBT1_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h5elo := hb5.1
  have h1elo := hb1.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · linarith only [h0, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]

theorem n7l_sBT1_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
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
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · rcases p0_3 (m.d 0 2) (by simp) with h71 | h71
      · rcases p0_3 (m.d 0 3) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 0 5) (by simp) with h75 | h75
            · linarith only [h75, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h70, h75, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h78 | h78
            · linarith only [h78, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h78, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h83 | h83
    · rcases p0_3 (m.d 0 2) (by simp) with h84 | h84
      · rcases p0_3 (m.d 0 3) (by simp) with h85 | h85
        · rcases p0_3 (m.d 0 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h88 | h88
            · linarith only [h88, hc04, hlam, hphi, ht45, p0_1, u5elo0]
            · linarith only [h83, h88, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h93, hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h100 | h100
    · rcases p0_3 (m.d 0 2) (by simp) with h101 | h101
      · linarith only [h101, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h103 | h103
        · rcases p0_3 (m.d 0 4) (by simp) with h104 | h104
          · rcases p0_3 (m.d 0 5) (by simp) with h105 | h105
            · linarith only [h105, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h100, h105, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h108 | h108
            · linarith only [h108, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h108, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h103, hlam, p0_0]
    · linarith only [h100, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
            · linarith only [h126, hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
        · linarith only [h123, hlam, p0_0]
    · linarith only [h114, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h133 | h133
    · rcases p0_3 (m.d 0 2) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h136 | h136
        · rcases p0_3 (m.d 0 4) (by simp) with h137 | h137
          · rcases p0_3 (m.d 0 5) (by simp) with h138 | h138
            · linarith only [h138, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h133, h138, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h137, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 0 5) (by simp) with h143 | h143
            · linarith only [h143, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h133, h143, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h142, hlam, p0_0]
    · linarith only [h133, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h148 | h148
    · rcases p0_3 (m.d 0 2) (by simp) with h149 | h149
      · rcases p0_3 (m.d 0 3) (by simp) with h150 | h150
        · linarith only [h150, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · linarith only [h153, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h148, h153, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h152, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · linarith only [h149, h160, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h148, h160, hc01, hlam, hphi, ht0b, ht5b, p0_1, u5ehi5]
          · linarith only [h159, hlam, p0_0]
    · linarith only [h148, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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

theorem n7l_sBT1_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h5bigk := hb5.1
  have h1elo := hb1.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h13 | h13
      · linarith only [h13, hc05, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h15 | h15
        · rcases p0_3 (m.d 3 5) (by simp) with h16 | h16
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · rcases m.htr 0 1 5 (by decide) (by decide) with h18 | h18
              · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
                · linarith only [h19, hlam, p0_0]
                · linarith only [h17, h19, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h13, h18, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 0 2 5 (by decide) (by decide) with h24 | h24
                · linarith only [h24, hlam, p0_0]
                · linarith only [h16, h24, hc02, hc35, hlam, hphi, ht23, p0_1]
              · linarith only [h13, h23, hlam]
          · rcases p0_3 (m.d 4 5) (by simp) with h28 | h28
            · rcases m.htr 0 1 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 0 2 5 (by decide) (by decide) with h30 | h30
                · linarith only [h30, hlam, p0_0]
                · linarith only [h28, h30, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h13, h29, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
                · linarith only [h35, hlam, p0_0]
                · linarith only [h35, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h13, h34, hlam]
        · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h42 | h42
      · linarith only [h42, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 5) (by simp) with h45 | h45
          · rcases p0_3 (m.d 4 5) (by simp) with h46 | h46
            · rcases m.htr 0 1 5 (by decide) (by decide) with h47 | h47
              · linarith only [h40, h47, hlam]
              · linarith only [h47, hc01, hc25, hlam, hphi, ht12, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h50 | h50
              · linarith only [h40, h50, hlam]
              · linarith only [h45, h50, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
              · linarith only [h40, h54, hlam]
              · linarith only [h53, h54, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h57 | h57
              · linarith only [h40, h57, hlam]
              · linarith only [h57, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h44, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h62 | h62
    · linarith only [h62, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h64 | h64
      · linarith only [h64, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h66 | h66
        · rcases p0_3 (m.d 3 5) (by simp) with h67 | h67
          · linarith only [h67, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 0 2 5 (by decide) (by decide) with h71 | h71
                · linarith only [h62, h70, h71, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h62, h71, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h64, h69, h70, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 2 5 (by decide) (by decide) with h76 | h76
                · linarith only [h62, h76, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h62, h76, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h64, h75, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h66, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h81 | h81
    · linarith only [h81, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h83 | h83
      · linarith only [h83, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 5) (by simp) with h86 | h86
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h87, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 2 5 (by decide) (by decide) with h90 | h90
                · linarith only [h81, h89, h90, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h81, h90, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h83, h86, h89, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · rcases p0_3 (m.d 4 5) (by simp) with h94 | h94
            · linarith only [h94, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
              · rcases m.htr 0 2 5 (by decide) (by decide) with h97 | h97
                · linarith only [h81, h97, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h81, h97, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h83, h96, hc01, hc25, hlam, hphi, ht12, p0_1]
        · linarith only [h85, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h102 | h102
    · linarith only [h102, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h104 | h104
      · linarith only [h104, hc05, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h106 | h106
        · rcases p0_3 (m.d 3 5) (by simp) with h107 | h107
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · rcases m.htr 0 1 5 (by decide) (by decide) with h109 | h109
              · rcases m.htr 0 2 5 (by decide) (by decide) with h110 | h110
                · linarith only [h106, h109, h110, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h108, h110, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h104, h109, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 0 2 5 (by decide) (by decide) with h115 | h115
                · linarith only [h106, h114, h115, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h106, h115, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h104, h114, hlam]
          · linarith only [h107, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h120 | h120
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 0 2 5 (by decide) (by decide) with h123 | h123
                · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                  · linarith only [h124, hlam, p0_0]
                  · linarith only [h121, h124, hc03, hc45, hlam, hphi, ht34, p0_1]
                · linarith only [h106, h123, hlam]
              · linarith only [h104, h122, hlam]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h129 | h129
              · rcases m.htr 0 2 5 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                  · linarith only [h131, hlam, p0_0]
                  · linarith only [h131, hc03, hc35, hlam, hphi, p0_1]
                · linarith only [h106, h130, hlam]
              · linarith only [h104, h129, hlam]
          · linarith only [h120, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h137 | h137
    · linarith only [h137, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h139 | h139
      · linarith only [h139, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h141 | h141
        · rcases p0_3 (m.d 3 5) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · rcases m.htr 0 1 5 (by decide) (by decide) with h144 | h144
              · linarith only [h137, h144, hlam]
              · linarith only [h143, h144, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h147 | h147
              · linarith only [h137, h147, hlam]
              · linarith only [h147, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h142, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h151 | h151
          · rcases p0_3 (m.d 4 5) (by simp) with h152 | h152
            · rcases m.htr 0 1 5 (by decide) (by decide) with h153 | h153
              · linarith only [h137, h153, hlam]
              · linarith only [h152, h153, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h156 | h156
              · linarith only [h137, h156, hlam]
              · linarith only [h156, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
    · linarith only [h160, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h162 | h162
      · linarith only [h162, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h164 | h164
        · linarith only [h164, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h166 | h166
          · rcases p0_3 (m.d 4 5) (by simp) with h167 | h167
            · rcases m.htr 0 1 5 (by decide) (by decide) with h168 | h168
              · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
                · linarith only [h160, h169, hlam]
                · linarith only [h169, hc02, hc35, hlam, hphi, ht23, p0_1]
              · linarith only [h162, h167, h168, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h173 | h173
              · rcases m.htr 0 2 5 (by decide) (by decide) with h174 | h174
                · linarith only [h160, h174, hlam]
                · linarith only [h174, hc02, hc35, hlam, hphi, ht23, p0_1]
              · linarith only [h162, h173, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h166, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h180 | h180
    · linarith only [h180, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h182 | h182
      · linarith only [h182, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h184 | h184
        · rcases p0_3 (m.d 3 5) (by simp) with h185 | h185
          · rcases p0_3 (m.d 4 5) (by simp) with h186 | h186
            · linarith only [h186, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h188 | h188
              · rcases m.htr 0 2 5 (by decide) (by decide) with h189 | h189
                · linarith only [h180, h184, h188, h189, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h180, h184, h189, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h182, h188, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h185, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h194 | h194
          · rcases p0_3 (m.d 4 5) (by simp) with h195 | h195
            · linarith only [h195, hlam, p0_0]
            · rcases m.htr 0 1 5 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 2 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 0 3 5 (by decide) (by decide) with h199 | h199
                  · linarith only [h180, h199, hc05, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                  · linarith only [h180, h199, hc03, hc35, hlam, hphi, p0_1]
                · linarith only [h184, h198, hc02, hc35, hlam, hphi, ht23, p0_1]
              · linarith only [h182, h197, hc01, hc35, hlam, hphi, ht12, ht23, p0_1]
          · linarith only [h194, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h205 | h205
    · linarith only [h205, hlam, p0_0]
    · rcases p0_3 (m.d 1 5) (by simp) with h207 | h207
      · linarith only [h207, hc05, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h209 | h209
        · rcases p0_3 (m.d 3 5) (by simp) with h210 | h210
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 2 5 (by decide) (by decide) with h213 | h213
                · linarith only [h209, h212, h213, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h213, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h207, h212, hlam]
            · linarith only [h211, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h218 | h218
            · rcases m.htr 0 1 5 (by decide) (by decide) with h219 | h219
              · rcases m.htr 0 2 5 (by decide) (by decide) with h220 | h220
                · linarith only [h209, h219, h220, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h220, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h207, h219, hlam]
            · linarith only [h218, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · rcases m.htr 0 1 5 (by decide) (by decide) with h227 | h227
              · rcases m.htr 0 2 5 (by decide) (by decide) with h228 | h228
                · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
                  · linarith only [h225, h227, h229, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo2]
                  · linarith only [h229, hc03, hc45, hlam, hphi, ht34, p0_1]
                · linarith only [h209, h228, hlam]
              · linarith only [h207, h227, hlam]
            · linarith only [h226, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h235 | h235
            · rcases m.htr 0 1 5 (by decide) (by decide) with h236 | h236
              · rcases m.htr 0 2 5 (by decide) (by decide) with h237 | h237
                · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
                    · linarith only [h239, hlam, p0_0]
                    · linarith only [h239, hc04, hc45, hlam, hphi, p0_1]
                  · linarith only [h225, h238, hlam]
                · linarith only [h209, h237, hlam]
              · linarith only [h207, h236, hlam]
            · linarith only [h235, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h246 | h246
    · linarith only [h246, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h248 | h248
      · linarith only [h248, hlam, p0_0]
      · rcases p0_3 (m.d 2 5) (by simp) with h250 | h250
        · rcases p0_3 (m.d 3 5) (by simp) with h251 | h251
          · rcases p0_3 (m.d 4 5) (by simp) with h252 | h252
            · rcases m.htr 0 1 5 (by decide) (by decide) with h253 | h253
              · linarith only [h246, h253, hlam]
              · linarith only [h253, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h257 | h257
            · rcases m.htr 0 1 5 (by decide) (by decide) with h258 | h258
              · linarith only [h246, h258, hlam]
              · linarith only [h258, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h257, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h262 | h262
          · rcases p0_3 (m.d 4 5) (by simp) with h263 | h263
            · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
              · linarith only [h246, h264, hlam]
              · linarith only [h264, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h263, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h268 | h268
            · rcases m.htr 0 1 5 (by decide) (by decide) with h269 | h269
              · linarith only [h246, h269, hlam]
              · linarith only [h269, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h268, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h273 | h273
    · linarith only [h273, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h275 | h275
      · linarith only [h275, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · rcases m.htr 0 1 5 (by decide) (by decide) with h281 | h281
              · rcases m.htr 0 2 5 (by decide) (by decide) with h282 | h282
                · linarith only [h273, h282, hlam]
                · linarith only [h282, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h275, h281, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h280, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h287 | h287
            · rcases m.htr 0 1 5 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 2 5 (by decide) (by decide) with h289 | h289
                · linarith only [h273, h289, hlam]
                · linarith only [h289, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h275, h288, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h287, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h294 | h294
    · linarith only [h294, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · rcases p0_3 (m.d 1 5) (by simp) with h296 | h296
      · linarith only [h296, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
      · rcases p0_3 (m.d 2 5) (by simp) with h298 | h298
        · rcases p0_3 (m.d 3 5) (by simp) with h299 | h299
          · linarith only [h299, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h301 | h301
            · rcases m.htr 0 1 5 (by decide) (by decide) with h302 | h302
              · rcases m.htr 0 2 5 (by decide) (by decide) with h303 | h303
                · linarith only [h294, h298, h302, h303, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo1]
                · linarith only [h294, h298, h303, hc02, hc25, hlam, hphi, p0_1]
              · linarith only [h296, h302, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h301, hlam, p0_0]
        · rcases p0_3 (m.d 3 5) (by simp) with h308 | h308
          · linarith only [h308, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h310 | h310
            · rcases m.htr 0 1 5 (by decide) (by decide) with h311 | h311
              · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
                · rcases m.htr 0 3 5 (by decide) (by decide) with h313 | h313
                  · linarith only [h294, h313, hlam]
                  · linarith only [h313, hc03, hc45, hlam, hphi, ht34, p0_1]
                · linarith only [h298, h312, hc02, hc45, hlam, hphi, ht23, ht34, p0_1]
              · linarith only [h296, h311, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p0_1]
            · linarith only [h310, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h4, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h4, h5, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h2, h4, h5, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
          · linarith only [h0, h6, hc24, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
            · linarith only [h13, h14, h2, h5, hc12, hlam, hphi, u1ehi0]
            · linarith only [h14, h2, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
          · linarith only [h13, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h4, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h19, hc24, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h22, h4, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h22, hc24, hlam, hphi, ht12, u1ehi0]

theorem n7l_sBT1_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5elo := hb5.1
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h0, h1, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h0, h1, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10 | h10
        · linarith only [h1, h10, h2, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
          · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h1, h12, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h15 | h15
      · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
        · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
          · linarith only [h1, h15, h17, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
            · linarith only [h0, h19, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h15, h19, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h1, h15, h16, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
        · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
          · linarith only [h0, h1, h24, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
            · linarith only [h0, h15, h26, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h28, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h28, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
          · linarith only [h0, h1, h31, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
            · linarith only [h0, h15, h33, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
              · linarith only [h0, h35, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h35, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h38 | h38
    · rcases m.htr 0 2 4 (by decide) (by decide) with h39 | h39
      · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
        · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
          · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
            · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                  · linarith only [h38, h45, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h40, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h38, h40, h44, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h43, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h39, h42, hlam]
          · linarith only [h0, h38, h41, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
          · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
            · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h38, h40, h56, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h38, h40, h52, h55, h58, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h58, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                  · linarith only [h38, h40, h61, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h38, h63, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h63, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h54, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h39, h53, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h38, h52, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
        · linarith only [h38, h39, h69, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
          · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
            · linarith only [h38, h39, h72, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                · linarith only [h71, h72, h75, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h38, h72, h75, h77, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h38, h79, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h79, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h74, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h38, h71, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h84 | h84
      · rcases m.htr 0 3 4 (by decide) (by decide) with h85 | h85
        · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
          · linarith only [h38, h84, h86, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
            · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
              · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h84, h91, h93, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h93, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h86, h92, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h86, h91, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h85, h86, h90, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h89, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h84, h88, hlam]
        · linarith only [h38, h84, h85, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
        · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
          · linarith only [h0, h103, h38, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
            · linarith only [h0, h105, h84, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h102, h111, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h111, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h110, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h103, h109, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h102, h108, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h107, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
          · linarith only [h0, h118, h38, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
            · linarith only [h0, h118, h120, h84, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                · linarith only [h0, h102, h123, h38, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                  · linarith only [h0, h118, h123, h125, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h118, h125, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h122, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem n7l_sBT1_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem n7l_sBT1_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
                · linarith only [h0, h2, h4, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h2, h4, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h0, h13, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h16, h2, h5, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, h2, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h2, h20, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h0, h2, h20, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h23 | h23
            · linarith only [h0, h2, h23, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h25 | h25
              · linarith only [h25, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h2, h27, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h29, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h2, h31, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h0, h2, h31, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h34 | h34
          · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
            · linarith only [h1, h2, h35, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
              · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
                · linarith only [h1, h2, h38, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h1, h2, h34, h4, h40, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                    · linarith only [h34, h4, h42, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h1, h2, h34, h35, h42, h44, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                        · linarith only [h1, h2, h46, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h1, h2, h37, h42, h46, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
              · linarith only [h34, h37, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h50 | h50
            · linarith only [h50, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
              · rcases m.htr 0 3 5 (by decide) (by decide) with h53 | h53
                · linarith only [h1, h2, h53, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h1, h2, h52, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h2, h57, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h2, h50, h59, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                        · linarith only [h1, h2, h61, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h1, h2, h52, h61, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
                · linarith only [h1, h2, h64, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h66, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                    · linarith only [h0, h2, h4, h68, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                      · linarith only [h0, h70, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                        · linarith only [h1, h2, h4, h52, h72, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                          · linarith only [h1, h64, h74, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                              · linarith only [h0, h2, h66, h72, h76, h77, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                                · linarith only [h1, h2, h68, h74, h77, h79, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                                    · rcases h5bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h2, hlam, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h50, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h64, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h66, hlam, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h68, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u1elo4]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h70, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h74, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h66, h68, h76, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p83_1, u1elo3]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h68, hc12, hc25, hlam, hphi, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h68, hc12, hc25, hlam, hphi, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h79, hlam, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h66, h68, h79, h82, hc12, hc34, hlam, hphi, ht23, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h68, h82, hc12, hc34, hlam, hphi, ht23, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h68, h82, hc12, hc34, hlam, hphi, ht23, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h0, h50, h82, hc12, hc34, hlam, hphi, ht23, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h66, h68, h82, hc12, hc34, hlam, hphi, ht23, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h1, h2, h68, hc12, hc45, hlam, hphi, ht23, ht34, p83_1]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h76, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h81, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [h82, hlam, p83_0]
                                      · have p83_0 := h83c.1
                                        have p83_1 := h83c.2.1
                                        have p83_2 := h83c.2.2.1
                                        have p83_3 := h83c.2.2.2
                                        linarith only [hlam, p83_0]
                                    · linarith only [h0, h34, h76, h77, h82, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                                  · linarith only [h0, h4, h76, h77, h81, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                                · linarith only [h1, h112, h2, h68, h74, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h111, h112, h4, h52, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                                · linarith only [h111, h115, h4, h64, hc02, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                                  · linarith only [h0, h117, h2, h76, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                                    · linarith only [h1, h117, h119, h2, h68, h70, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h111, h119, h4, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h122 | h122
      · linarith only [h122, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h124 | h124
        · linarith only [h0, h1, h124, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h126 | h126
          · rcases m.htr 0 2 5 (by decide) (by decide) with h127 | h127
            · linarith only [h0, h127, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h129 | h129
              · rcases m.htr 0 3 5 (by decide) (by decide) with h130 | h130
                · linarith only [h130, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h1, h126, h130, h132, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                    · linarith only [h124, h126, h134, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h136 | h136
                      · linarith only [h0, h1, h126, h127, h130, h136, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h1, h130, h139, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h1, h139, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h129, h138, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h1, h126, h129, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h144 | h144
            · linarith only [h0, h144, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h146 | h146
              · rcases m.htr 0 3 5 (by decide) (by decide) with h147 | h147
                · linarith only [h147, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
                  · linarith only [h149, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · linarith only [h0, h1, h147, h151, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                      · linarith only [h0, h1, h144, h147, h153, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h156 | h156
                          · linarith only [h1, h147, h156, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h1, h156, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h155, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h160 | h160
                · linarith only [h160, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h162, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                    · linarith only [h0, h164, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h166, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                        · linarith only [h1, h146, h168, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h168, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h171 | h171
    · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
      · linarith only [h172, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h174 | h174
        · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
          · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
            · linarith only [h176, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
              · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                · linarith only [h0, h171, h176, h179, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h181 | h181
                  · linarith only [h181, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                      · linarith only [h0, h176, h184, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                        · linarith only [h171, h186, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h171, h176, h178, h183, h186, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h174, h176, h183, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
                · linarith only [h171, h190, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h192 | h192
                  · linarith only [h175, h176, h192, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h171, h176, h194, h195, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                        · linarith only [h171, h178, h197, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                          · linarith only [h171, h190, h199, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                              · linarith only [h0, h171, h178, h192, h194, h197, h201, h202, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                                · linarith only [h0, h171, h194, h195, h199, h204, hlam]
                                · linarith only [h0, h171, h194, h195, h204, hc23, hc35, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                              · linarith only [h171, h178, h194, h207, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                                · linarith only [h0, h171, h194, h195, h209, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                · linarith only [h0, h171, h194, h195, h209, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h174, h176, h194, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h213 | h213
            · linarith only [h213, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
              · linarith only [h0, h171, h175, h215, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h217 | h217
                · linarith only [h171, h217, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h219, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h213, h222, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                        · linarith only [h171, h215, h224, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
                          · linarith only [h0, h171, h175, h217, h219, h226, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                            · linarith only [h0, h175, h219, h228, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                              · linarith only [h0, h171, h175, h215, h221, h230, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                                · linarith only [h171, h221, h226, h232, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
                                · linarith only [h0, h171, h221, h222, h232, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h171, h174, h221, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h171, h174, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h237 | h237
      · linarith only [h237, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h239 | h239
        · rcases m.htr 0 2 4 (by decide) (by decide) with h240 | h240
          · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
            · linarith only [h241, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
                · linarith only [h239, h241, h244, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h239, h241, h243, h246, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                      · linarith only [h171, h239, h241, h249, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                          · linarith only [h243, h244, h252, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h254 | h254
                            · linarith only [h239, h241, h246, h251, h252, h254, hc23, hc35, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                              · linarith only [h239, h256, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h243, h256, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h171, h243, h251, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h239, h241, h248, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
                · linarith only [h240, h241, h243, h261, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                  · linarith only [h240, h241, h263, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h239, h241, h266, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                        · linarith only [h171, h243, h268, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
                          · linarith only [h171, h261, h268, h270, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h171, h243, h263, h272, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                              · linarith only [h239, h274, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                                · linarith only [h239, h270, h276, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                                  · linarith only [h240, h241, h272, h278, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                                    · linarith only [h0, h266, h278, h280, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h171, h268, h280, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h239, h240, h265, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h284 | h284
            · linarith only [h240, h284, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h286 | h286
              · linarith only [h239, h240, h286, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h288 | h288
                · linarith only [h239, h240, h288, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h290, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h239, h284, h293, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                        · linarith only [h171, h286, h295, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                          · linarith only [h171, h288, h295, h297, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h299 | h299
                            · linarith only [h239, h240, h290, h299, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                              · linarith only [h171, h239, h295, h301, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                                · linarith only [h171, h239, h297, h303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                                  · linarith only [h239, h240, h290, h301, h305, hc23, hc34, hlam, hphi]
                                  · linarith only [h239, h240, h305, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h239, h292, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
          · rcases m.htr 0 2 5 (by decide) (by decide) with h310 | h310
            · linarith only [h239, h310, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h312 | h312
              · rcases m.htr 0 3 5 (by decide) (by decide) with h313 | h313
                · linarith only [h313, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                  · linarith only [h239, h309, h313, h315, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                    · linarith only [h239, h309, h317, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                      · linarith only [h309, h310, h319, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                          · linarith only [h239, h309, h313, h322, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                            · linarith only [h321, h322, h324, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                                · linarith only [h0, h317, h322, h327, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h317, h327, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h317, h326, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h171, h312, h321, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h239, h309, h312, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
            · linarith only [h333, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h335 | h335
              · rcases m.htr 0 3 5 (by decide) (by decide) with h336 | h336
                · linarith only [h336, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h338 | h338
                  · linarith only [h335, h336, h338, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                    · linarith only [h0, h239, h340, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                      · linarith only [h0, h333, h342, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                          · linarith only [h335, h336, h345, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                            · linarith only [h0, h309, h338, h347, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                                · linarith only [h0, h340, h345, h350, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h340, h350, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h335, h340, h349, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h171, h335, h344, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h355 | h355
                · linarith only [h355, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
                  · linarith only [h357, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h359 | h359
                    · linarith only [h0, h239, h359, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h361 | h361
                      · linarith only [h0, h333, h361, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                        · linarith only [h171, h335, h363, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
                          · linarith only [h0, h239, h355, h363, h365, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h367 | h367
                            · linarith only [h0, h309, h357, h367, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
                              · linarith only [h0, h359, h363, h369, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h359, h369, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sBT1_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h2, h4, hc13, hlam, hphi, u1ehi0]
      · linarith only [h0, h4, hc35, hlam, hphi, ht12, ht23, u1ehi0]

theorem n7l_sBT1_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
  · linarith only [h0, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem n7l_sBT1_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · linarith only [h0, h1, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h6, h8, hc01, hlam, hphi, u1elo2]
        · linarith only [h0, h8, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem n7l_sBT1_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
    · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem n7l_sBT1_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sBT1_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sBT1_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h1bigk := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h11, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h10, h13, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h11, h13, h16, h3, h4, h5, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                              · linarith only [h13, h15, h18, h6, h8, hlam]
                              · linarith only [h0, h15, h18, h3, h4, h5, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h10, h11, h15, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h0, h10, h22, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h24, h7, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                          · linarith only [h0, h10, h24, h26, h3, h4, h5, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                            · linarith only [h0, h22, h28, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                              · linarith only [h24, h30, h7, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                                · linarith only [h26, h30, h32, h7, h8, hc23, hc34, hlam, hphi]
                                · rcases h1bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    rcases p34_3 (m.d 0 1) (by simp) with h36 | h36
                                    · rcases p34_3 (m.d 1 2) (by simp) with h37 | h37
                                      · linarith only [h37, hlam, p34_0]
                                      · rcases p34_3 (m.d 1 3) (by simp) with h39 | h39
                                        · linarith only [h1, h10, h39, hlam]
                                        · rcases p34_3 (m.d 1 4) (by simp) with h41 | h41
                                          · linarith only [h1, h41, hlam]
                                          · rcases p34_3 (m.d 1 5) (by simp) with h43 | h43
                                            · linarith only [h2, h43, hlam]
                                            · linarith only [h43, h8, hlam]
                                    · linarith only [h36, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h0, h10, h3, h32, h4, h5, hlam, p34_2]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    rcases p34_3 (m.d 0 1) (by simp) with h48 | h48
                                    · rcases p34_3 (m.d 1 2) (by simp) with h49 | h49
                                      · linarith only [h0, h49, hlam]
                                      · linarith only [h49, h7, hlam]
                                    · linarith only [h48, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h0, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h28, h3, h32, h4, h5, h8, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h28, h3, h32, h4, h5, h8, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h8, hlam, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h0, h3, h4, h5, hc13, hlam, hphi, ht01, ht0b, ht5b, p34_1, u5ehi0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h6, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h10, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h22, hlam, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h1, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h7, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h0, h28, h3, h32, h4, h5, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h24, hlam, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h2, hlam, p34_0]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    rcases p34_3 (m.d 0 1) (by simp) with h71 | h71
                                    · rcases p34_3 (m.d 1 2) (by simp) with h72 | h72
                                      · linarith only [h72, h8, hlam]
                                      · linarith only [h6, h72, hlam]
                                    · linarith only [h0, h6, h71, hlam]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    rcases p34_3 (m.d 0 1) (by simp) with h76 | h76
                                    · rcases p34_3 (m.d 1 2) (by simp) with h77 | h77
                                      · linarith only [h77, h8, hlam]
                                      · linarith only [h7, h77, hlam]
                                    · linarith only [h1, h76, hlam]
                                  · have p34_0 := h34c.1
                                    have p34_1 := h34c.2.1
                                    have p34_2 := h34c.2.2.1
                                    have p34_3 := h34c.2.2.2
                                    linarith only [hlam, p34_0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h7, h82, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                    · linarith only [h6, h7, h84, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h84, h86, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h88 | h88
                        · linarith only [h0, h3, h4, h84, h88, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                          · linarith only [h0, h3, h4, h5, h6, h7, h88, h90, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                            · linarith only [h0, h3, h4, h5, h6, h7, h86, h88, h92, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                              · linarith only [h6, h7, h88, h90, h94, hc23, hc34, hlam, hphi]
                              · linarith only [h0, h3, h4, h5, h6, h7, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                  · linarith only [h6, h98, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
                      · linarith only [h0, h101, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                        · linarith only [h0, h103, h3, h6, h97, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                            · linarith only [h0, h106, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                              · linarith only [h106, h108, h6, h97, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h110 | h110
                                · linarith only [h105, h106, h108, h110, h6, h97, hlam]
                                · linarith only [h0, h106, h110, h3, h4, h5, h6, h97, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h105, h3, h4, h6, h97, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h100, h6, h97, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                      · linarith only [h0, h118, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                        · linarith only [h1, h120, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                            · linarith only [h0, h123, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                              · linarith only [h120, h122, h123, h125, h97, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                                · linarith only [h125, h127, h97, hc12, hc34, hlam, hphi, ht23]
                                · rcases h1bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h0, h122, h123, h127, h3, h4, h5, h97, hlam, p129_2]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    rcases p129_3 (m.d 0 1) (by simp) with h132 | h132
                                    · rcases p129_3 (m.d 1 2) (by simp) with h133 | h133
                                      · linarith only [h0, h133, hlam]
                                      · rcases p129_3 (m.d 1 3) (by simp) with h135 | h135
                                        · linarith only [h135, hlam, p129_0]
                                        · rcases p129_3 (m.d 1 4) (by simp) with h137 | h137
                                          · linarith only [h1, h137, hlam]
                                          · rcases p129_3 (m.d 1 5) (by simp) with h139 | h139
                                            · linarith only [h139, h2, hlam]
                                            · linarith only [h118, h139, hlam]
                                    · linarith only [h132, hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    rcases p129_3 (m.d 0 1) (by simp) with h143 | h143
                                    · rcases p129_3 (m.d 1 2) (by simp) with h144 | h144
                                      · linarith only [h0, h144, hlam]
                                      · rcases p129_3 (m.d 1 3) (by simp) with h146 | h146
                                        · linarith only [h0, h123, h127, h146, h3, h4, h5, h6, hlam]
                                        · linarith only [h117, h146, hlam]
                                    · linarith only [h143, hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h0, hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h6, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h97, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h115, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h0, h123, h127, h3, h4, h5, h6, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h0, h123, h127, h3, h4, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h0, h123, h127, h3, h4, h5, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h118, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h1, hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h0, h122, h123, h127, h3, h4, h5, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h117, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h120, hlam, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h2, hlam, p129_0]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    rcases p129_3 (m.d 0 1) (by simp) with h167 | h167
                                    · rcases p129_3 (m.d 1 2) (by simp) with h168 | h168
                                      · linarith only [h115, h168, hlam]
                                      · rcases p129_3 (m.d 1 3) (by simp) with h170 | h170
                                        · linarith only [h118, h170, hlam]
                                        · linarith only [h170, h6, hlam]
                                    · linarith only [h0, h167, hlam]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [h117, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    rcases p129_3 (m.d 0 1) (by simp) with h175 | h175
                                    · rcases p129_3 (m.d 1 2) (by simp) with h176 | h176
                                      · linarith only [h115, h176, hlam]
                                      · rcases p129_3 (m.d 1 3) (by simp) with h178 | h178
                                        · linarith only [h118, h178, hlam]
                                        · linarith only [h117, h178, hlam]
                                    · linarith only [h1, h175, hlam]
                                  · have p129_0 := h129c.1
                                    have p129_1 := h129c.2.1
                                    have p129_2 := h129c.2.2.1
                                    have p129_3 := h129c.2.2.2
                                    linarith only [hlam, p129_0]
                          · linarith only [h117, h122, h6, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                      · linarith only [h1, h117, h184, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                        · linarith only [h0, h117, h186, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                            · linarith only [h0, h184, h189, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · linarith only [h117, h188, h189, hc13, hc35, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                            · linarith only [h188, h192, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
                              · linarith only [h0, h188, h194, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                                · linarith only [h0, h196, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h188, h196, h6, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc15, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc14, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT1_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h5, h6, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h12, h5, h6, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h11, h12, h14, h5, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h11, h14, h5, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h11, h8, h9, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h1, h18, h3, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h20, h8, hc23, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h18, h22, h5, h6, hc25, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h0, h2, h24, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                          · linarith only [h24, h26, h5, h6, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h1, h26, h3, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h1, h29, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h1, h32, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h0, h1, h31, h32, h35, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h35, h5, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h34, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h0, h1, h39, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                    · linarith only [h0, h1, h31, h41, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · linarith only [h0, h1, h3, h41, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
        · linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc24, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT1_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sBT1_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h1ehi := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
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
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h15, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h0, h12, h14, h15, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                                · linarith only [h0, h14, h18, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                                  · linarith only [h0, h11, h20, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h0, h11, h13, h14, h20, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h24, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h0, h12, h23, h24, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                                · linarith only [h0, h11, h13, h23, h27, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                  · linarith only [h11, h13, h29, hlam]
                                  · rcases h5bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [hlam, p31_0]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      rcases p31_3 (m.d 0 5) (by simp) with h33 | h33
                                      · rcases p31_3 (m.d 1 5) (by simp) with h34 | h34
                                        · linarith only [h2, h34, hlam]
                                        · rcases p31_3 (m.d 2 5) (by simp) with h36 | h36
                                          · linarith only [h36, h5, hlam]
                                          · rcases p31_3 (m.d 3 5) (by simp) with h38 | h38
                                            · linarith only [h38, h7, hlam]
                                            · rcases p31_3 (m.d 4 5) (by simp) with h40 | h40
                                              · linarith only [h40, h8, hlam]
                                              · linarith only [h13, h40, hlam]
                                      · linarith only [h2, h33, hlam]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      rcases p31_3 (m.d 0 5) (by simp) with h44 | h44
                                      · rcases p31_3 (m.d 1 5) (by simp) with h45 | h45
                                        · linarith only [h2, h45, hlam]
                                        · linarith only [h10, h45, hlam]
                                      · linarith only [h44, h5, hlam]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      rcases p31_3 (m.d 0 5) (by simp) with h49 | h49
                                      · rcases p31_3 (m.d 1 5) (by simp) with h50 | h50
                                        · linarith only [h2, h50, hlam]
                                        · linarith only [h12, h50, hlam]
                                      · linarith only [h49, h7, hlam]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h0, h13, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p31_1, u1ehi3]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h2, hlam, p31_0]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [hlam, p31_0]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi2]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h2, h23, h29, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h13, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h5, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h10, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [hlam, p31_0]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h27, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h13, hc25, hlam, hphi, ht12, p31_1, u1ehi4]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h7, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h12, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h0, h3, h7, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi2]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [hlam, p31_0]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h29, hlam, p31_1]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h8, hlam, p31_0]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h0, h13, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p31_1, u1ehi3]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi2]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi3]
                                    · have p31_0 := h31c.1
                                      have p31_1 := h31c.2.1
                                      have p31_2 := h31c.2.2.1
                                      have p31_3 := h31c.2.2.2
                                      linarith only [hlam, p31_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h0, h11, h12, h3, h7, h75, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h12, h78, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                                  · linarith only [h75, h80, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                  · rcases h5bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      rcases p82_3 (m.d 0 5) (by simp) with h84 | h84
                                      · rcases p82_3 (m.d 1 5) (by simp) with h85 | h85
                                        · linarith only [h2, h85, hlam]
                                        · rcases p82_3 (m.d 2 5) (by simp) with h87 | h87
                                          · linarith only [h5, h87, hlam]
                                          · rcases p82_3 (m.d 3 5) (by simp) with h89 | h89
                                            · linarith only [h7, h89, hlam]
                                            · linarith only [h12, h89, hlam]
                                      · linarith only [h2, h84, hlam]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      rcases p82_3 (m.d 0 5) (by simp) with h93 | h93
                                      · rcases p82_3 (m.d 1 5) (by simp) with h94 | h94
                                        · linarith only [h2, h94, hlam]
                                        · linarith only [h10, h94, hlam]
                                      · linarith only [h5, h93, hlam]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h11, h12, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h3, h6, h75, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h2, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p82_1, u5ehi2]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h12, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h75, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h5, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h10, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h78, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h12, h80, hc25, hlam, hphi, ht12, p82_1, u1ehi4]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h7, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h80, hc45, hlam, hphi, ht12, ht23, ht34, p82_1, u1ehi4]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h3, h7, hc01, hlam, hphi, ht0b, ht5b, p82_1, u5ehi2]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h80, hlam, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h8, hlam, p82_0]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h11, h12, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h3, h6, h77, h78, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p82_1]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p82_1, u5ehi3]
                                    · have p82_0 := h82c.1
                                      have p82_1 := h82c.2.1
                                      have p82_2 := h82c.2.2.1
                                      have p82_3 := h82c.2.2.2
                                      linarith only [hlam, p82_0]
                              · linarith only [h11, h12, h77, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h0, h11, h121, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                              · linarith only [h11, h124, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                                · linarith only [h121, h126, h9, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h128 | h128
                                  · rcases h5bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      rcases p129_3 (m.d 0 5) (by simp) with h131 | h131
                                      · rcases p129_3 (m.d 1 5) (by simp) with h132 | h132
                                        · linarith only [h132, h2, hlam]
                                        · rcases p129_3 (m.d 2 5) (by simp) with h134 | h134
                                          · linarith only [h134, h5, hlam]
                                          · rcases p129_3 (m.d 3 5) (by simp) with h136 | h136
                                            · linarith only [h136, h7, hlam]
                                            · linarith only [h121, h136, hlam]
                                      · linarith only [h131, h2, hlam]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      rcases p129_3 (m.d 0 5) (by simp) with h140 | h140
                                      · rcases p129_3 (m.d 1 5) (by simp) with h141 | h141
                                        · linarith only [h141, h2, hlam]
                                        · linarith only [h10, h141, hlam]
                                      · linarith only [h140, h5, hlam]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h121, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p129_1, u1ehi2]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      rcases p129_3 (m.d 0 5) (by simp) with h146 | h146
                                      · rcases p129_3 (m.d 1 5) (by simp) with h147 | h147
                                        · linarith only [h147, h2, hlam]
                                        · linarith only [h123, h147, hlam]
                                      · linarith only [h146, h8, hlam]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h2, hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi2]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h121, hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h11, h123, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi4]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h5, hlam, p129_1]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h10, hlam, p129_1]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h126, hlam, p129_1]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi4]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h7, hlam, p129_1]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h128, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi1]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h128, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi2]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h128, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi4]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h8, hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h123, hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p129_1, u5ehi2]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [h128, hlam, p129_0]
                                    · have p129_0 := h129c.1
                                      have p129_1 := h129c.2.1
                                      have p129_2 := h129c.2.2.1
                                      have p129_3 := h129c.2.2.2
                                      linarith only [hlam, p129_0]
                                  · linarith only [h11, h123, h128, hc15, hlam, hphi, u1ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                              · linarith only [h11, h172, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                                · linarith only [h0, h11, h174, h3, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
                                  · linarith only [h0, h11, h123, h176, h3, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                  · linarith only [h11, h176, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h180 | h180
                          · linarith only [h0, h10, h180, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                            · linarith only [h0, h10, h179, h182, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                              · linarith only [h0, h10, h184, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h10, h179, h184, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                          · linarith only [h0, h10, h187, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                              · linarith only [h179, h190, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                                · linarith only [h187, h192, h9, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                                  · rcases h5bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      rcases p195_3 (m.d 0 5) (by simp) with h197 | h197
                                      · rcases p195_3 (m.d 1 5) (by simp) with h198 | h198
                                        · linarith only [h198, h2, hlam]
                                        · rcases p195_3 (m.d 2 5) (by simp) with h200 | h200
                                          · linarith only [h200, h5, hlam]
                                          · linarith only [h10, h200, hlam]
                                      · linarith only [h197, h2, hlam]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, h10, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p195_1, u1ehi2]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, h187, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p195_1, u1ehi2]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      rcases p195_3 (m.d 0 5) (by simp) with h206 | h206
                                      · rcases p195_3 (m.d 1 5) (by simp) with h207 | h207
                                        · linarith only [h2, h207, hlam]
                                        · linarith only [h189, h207, hlam]
                                      · linarith only [h206, h8, hlam]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h2, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h10, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h187, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi4]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h5, hlam, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht12, p195_1, u1ehi4]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h192, hlam, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, h192, h194, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi4]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h7, hlam, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, h10, h194, h3, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p195_1, u1ehi2]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, h194, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi2]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, h194, h3, h6, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi4]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h8, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h189, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h10, h9, hc45, hlam, hphi, ht12, ht23, ht34, p195_1, u1ehi2]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h194, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                  · linarith only [h179, h189, h194, hc15, hlam, hphi, u1ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                              · linarith only [h179, h232, h9, hc12, hlam, hphi, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                                · linarith only [h0, h10, h234, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                                  · linarith only [h0, h179, h189, h236, h3, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                  · linarith only [h0, h179, h236, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                      · linarith only [h0, h239, h3, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h246 | h246
                                  · linarith only [h1, h241, h246, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h5bigk with h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      rcases p248_3 (m.d 0 5) (by simp) with h250 | h250
                                      · rcases p248_3 (m.d 1 5) (by simp) with h251 | h251
                                        · linarith only [h2, h251, hlam]
                                        · rcases p248_3 (m.d 2 5) (by simp) with h253 | h253
                                          · linarith only [h253, h5, hlam]
                                          · linarith only [h239, h253, hlam]
                                      · linarith only [h2, h250, hlam]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h0, h239, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p248_1, u1ehi1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      rcases p248_3 (m.d 0 5) (by simp) with h258 | h258
                                      · rcases p248_3 (m.d 1 5) (by simp) with h259 | h259
                                        · linarith only [h2, h259, hlam]
                                        · linarith only [h242, h259, hlam]
                                      · linarith only [h258, h7, hlam]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      rcases p248_3 (m.d 0 5) (by simp) with h263 | h263
                                      · rcases p248_3 (m.d 1 5) (by simp) with h264 | h264
                                        · linarith only [h2, h264, hlam]
                                        · linarith only [h243, h264, hlam]
                                      · linarith only [h263, h8, hlam]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h2, hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h239, hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p248_1, u5ehi3]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h2, h246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p248_1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h5, hlam, p248_1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht12, p248_1, u1ehi4]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h0, h245, h3, hc01, hlam, hphi, ht0b, ht5b, p248_1, u5ehi3]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h0, h245, h246, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p248_1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h7, hlam, p248_1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h242, hlam, p248_1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h245, hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h246, hlam, p248_1]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h8, hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h243, hlam, p248_0]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p248_1, u5ehi2]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [h2, h243, hc01, hlam, hphi, ht0b, ht5b, p248_1, u5ehi3]
                                    · have p248_0 := h248c.1
                                      have p248_1 := h248c.2.1
                                      have p248_2 := h248c.2.2.1
                                      have p248_3 := h248c.2.2.2
                                      linarith only [hlam, p248_0]
                                · linarith only [h0, h241, h243, h245, h3, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h244, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
                                  · linarith only [h241, h243, h292, hc13, hlam, hphi, u1ehi3]
                                  · rcases h5bigk with h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      rcases p294_3 (m.d 0 5) (by simp) with h296 | h296
                                      · rcases p294_3 (m.d 1 5) (by simp) with h297 | h297
                                        · linarith only [h2, h297, hlam]
                                        · rcases p294_3 (m.d 2 5) (by simp) with h299 | h299
                                          · linarith only [h299, h5, hlam]
                                          · linarith only [h239, h299, hlam]
                                      · linarith only [h2, h296, hlam]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h0, h239, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p294_1, u1ehi1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      rcases p294_3 (m.d 0 5) (by simp) with h304 | h304
                                      · rcases p294_3 (m.d 1 5) (by simp) with h305 | h305
                                        · linarith only [h2, h305, hlam]
                                        · linarith only [h242, h305, hlam]
                                      · linarith only [h304, h7, hlam]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h0, h243, h3, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p294_1, u1ehi3]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h2, hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h239, hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p294_1, u5ehi3]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h243, hlam, p294_1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h5, hlam, p294_1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht12, p294_1, u1ehi4]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h0, h291, h3, hc01, hlam, hphi, ht0b, ht5b, p294_1, u5ehi3]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h0, h243, h291, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p294_1, u1ehi3]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h7, hlam, p294_1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h242, hlam, p294_1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h291, hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h292, hlam, p294_1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h8, hlam, p294_0]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h239, hc45, hlam, hphi, ht12, ht23, ht34, p294_1, u1ehi1]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p294_1, u5ehi2]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, p294_1, u5ehi3]
                                    · have p294_0 := h294c.1
                                      have p294_1 := h294c.2.1
                                      have p294_2 := h294c.2.2.1
                                      have p294_3 := h294c.2.2.2
                                      linarith only [hlam, p294_0]
                                · linarith only [h0, h291, h3, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h290, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
                            · linarith only [h0, h241, h242, h3, h332, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h335 | h335
                                · linarith only [h242, h335, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h0, h3, h335, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h241, h242, h3, h334, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
                          · linarith only [h0, h241, h3, h339, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                              · linarith only [h241, h342, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h3, h342, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                              · linarith only [h241, h345, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h345, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                · linarith only [h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc25, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h3, h4, hc24, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc15, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT1_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
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
        · linarith only [h3, hlam, hphi, ht01, u0ehi0, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi1, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sBT1_M_IR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo4]

theorem n7l_sBT1_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
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
        · linarith only [h3, hlam, hphi, ht01, u0ehi0, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi1, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sBT1_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
      · linarith only [h2, hlam, hphi, ht01, u0ehi0, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sBT1_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1ehi := hb1.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo3]
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo4]
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

theorem n7l_sBT1_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
            · rcases h0emin with h8 | h8 | h8 | h8 | h8
              · linarith only [h8, hlam, ht01, u1elo0]
              · linarith only [h0, h8, hlam, ht01, u1elo0]
              · linarith only [h0, h2, h8, hlam, ht01, u1elo0]
              · linarith only [h1, h8, hlam, ht01, u1elo0]
              · linarith only [h8, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h15 | h15
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
          · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
          · linarith only [h15, h16, h2, hc12, hc23, hlam, hphi]
        · linarith only [h15, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht01, u0ehi0, u1elo3]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sBT1_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem n7l_sBT1_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h3, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                · linarith only [h1, h6, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h1, h11, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h1, h14, h3, h4, h6, h8, hc25, hlam, hphi, ht12, u1ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h1, h11, h13, h14, h16, h3, h4, h8, hc35, hlam, hphi, ht0b, ht12, ht23, ht5b, u0elo0, u1ehi3, u5ehi1]
                        · linarith only [h13, h14, h16, h3, h4, hc34, hc45, hlam, hphi]
                    · linarith only [h1, h13, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                · linarith only [h2, h20, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h2, h22, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                    · linarith only [h24, h8, hc23, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h26, h3, h6, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h22, h28, h8, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · linarith only [h28, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
          · linarith only [h31, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
            · linarith only [h1, h33, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
              · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                · linarith only [h1, h36, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h1, h35, h38, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h1, h33, h41, hc23, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h0, h3, h41, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h0, h1, h3, h35, h40, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                · linarith only [h2, h35, h45, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                  · linarith only [h2, h47, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                    · linarith only [h35, h49, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h0, h3, h49, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h54 | h54
    · linarith only [h0, h54, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
      · linarith only [h0, h56, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h58 | h58
        · rcases m.htr 0 2 5 (by decide) (by decide) with h59 | h59
          · linarith only [h59, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
            · linarith only [h58, h59, h61, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
              · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                · linarith only [h54, h61, h64, hc13, hlam, hphi, u1ehi0]
                · linarith only [h54, h64, hc35, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h54, h63, hc34, hlam, hphi, ht12, ht23, u1ehi0]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
          · linarith only [h68, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
            · linarith only [h70, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                · linarith only [h0, h58, h70, h73, hc13, hlam, hphi, u1ehi0]
                · linarith only [h54, h73, hc35, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h54, h72, hc34, hlam, hphi, ht12, ht23, u1ehi0]

theorem n7l_sBT1_M_LI_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h11, h14, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h13, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                          · linarith only [h11, h12, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h0, h11, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                      · linarith only [h10, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                    · linarith only [h0, h4, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · linarith only [h2, h8, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                        · linarith only [h24, h26, h28, h3, h6, hc12, hlam, hphi, u1ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                              · linarith only [h0, h24, h26, h3, h32, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                                · linarith only [h0, h26, h34, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h24, h34, h6, hc23, hc34, hlam, hphi]
                            · linarith only [h28, h30, h31, hc35, hlam, hphi, u5elo4]
                          · linarith only [h30, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
                      · linarith only [h27, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                    · linarith only [h0, h26, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                  · linarith only [h24, h25, h6, hc35, hlam, hphi, u5elo4]
                · linarith only [h1, h24, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
            · linarith only [h0, h5, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h44 | h44
            · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
              · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                    · linarith only [h3, h4, h44, h48, hc12, hlam, hphi, u1ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                                  · linarith only [h1, h51, h56, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h2, h53, h56, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h3, h4, h44, h55, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                              · linarith only [h3, h4, h44, h54, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                            · linarith only [h53, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                          · linarith only [h48, h50, h52, hc25, hlam, hphi, u5elo3]
                        · linarith only [h1, h45, h48, h50, h51, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h50, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                  · linarith only [h2, h47, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h1, h46, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h67 | h67
                · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                    · linarith only [h3, h4, h44, h69, hc12, hlam, hphi, u1ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                        · linarith only [h1, h45, h72, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                              · linarith only [h3, h4, h44, h45, h76, hc23, hlam, hphi, ht12, u1ehi4]
                              · linarith only [h3, h4, h44, h76, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                            · linarith only [h72, h74, h75, hc35, hlam, hphi, u5elo4]
                          · linarith only [h69, h71, h74, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo3]
                      · linarith only [h71, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
                  · linarith only [h3, h4, h44, h45, h68, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo4]
                · linarith only [h3, h4, h44, h67, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo3]
            · linarith only [h0, h44, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
      · linarith only [h1, h2, hc14, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
    · linarith only [h0, h88, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h90 | h90
      · linarith only [h0, h90, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
        · linarith only [h0, h92, hc12, hlam, hphi, u1ehi4]
        · linarith only [h92, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem n7l_sBT1_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
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
            · linarith only [h38, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
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
            · linarith only [h55, h63, hc03, hlam, hphi, ht34, ht45, p0_1, u5elo0]
            · linarith only [h63, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi5]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0, u5ehi5]
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
            · linarith only [h93, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
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
            · linarith only [h107, h88, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u5elo0]
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
            · linarith only [h116, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
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
            · linarith only [h165, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
          · rcases p0_3 (m.d 0 5) (by simp) with h168 | h168
            · linarith only [h168, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
            · linarith only [h168, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
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
            · linarith only [h185, h189, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
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
            · linarith only [h200, h211, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
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
            · linarith only [h244, h246, hlam, hphi, ht0b, ht5b, p0_1, u0elo2, u5ehi5]
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
            · linarith only [h264, hc02, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo0]
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
            · linarith only [h269, h273, hlam, hphi, ht0b, ht5b, p0_1, u0elo1, u5ehi5]
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

theorem n7l_sBT1_M_LI_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h1, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h10 | h10
      · linarith only [h0, h10, hc12, hlam, hphi, u1ehi4]
      · linarith only [h10, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem n7l_sBT1_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5bigk := hb5.1
  have h1elo := hb1.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
    · linarith only [h12, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h12, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h16 | h16
    · linarith only [h16, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h16, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h19 | h19
    · linarith only [h19, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h19, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h23, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
    · linarith only [h26, hc25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h26, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h30 | h30
    · linarith only [h30, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h30, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
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

theorem n7l_sBT1_M_LR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1ehi := hb1.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hc25, hlam, hphi, ht12, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h20 | h20
    · linarith only [h20, hc35, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h20, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
    · linarith only [h23, hc45, hlam, hphi, ht0b, ht5b, p0_1, u0elo4]
    · linarith only [h23, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht12, ht23, p0_1, u1ehi4]
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
    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi4]
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

theorem n7l_sBT1_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sBT1_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo4]

theorem n7l_sBT1_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h1, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h1, h3, h8, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h1, h12, h5, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h1, h10, h12, h15, h7, h8, hc25, hlam, hphi, ht01, ht12, u0ehi8]
                        · linarith only [h0, h1, h10, h15, hc23, hc35, hlam, hphi]
                      · linarith only [h14, h7, h8, hc13, hc35, hlam, hphi]
                  · linarith only [h10, h11, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h10, h3, h5, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h25, h5, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                      · linarith only [h27, h7, hc13, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h0, h1, h21, h24, h25, h27, h29, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h0, h1, h23, h29, hc23, hc35, hlam, hphi]
                  · linarith only [h23, h24, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h23, h3, h5, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h34 | h34
          · linarith only [h0, h1, h34, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36 | h36
            · linarith only [h3, h36, h4, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
              · linarith only [h36, h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h4, h41, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h0, h1, h3, h34, h43, hc15, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                      · linarith only [h36, h45, hc13, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h0, h1, h38, h40, h43, h47, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h0, h1, h40, h47, hc23, hc35, hlam, hphi]
                · linarith only [h3, h4, h40, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h51 | h51
        · rcases m.htr 0 2 5 (by decide) (by decide) with h52 | h52
          · linarith only [h52, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h54 | h54
            · rcases m.htr 0 3 5 (by decide) (by decide) with h55 | h55
              · linarith only [h55, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                · linarith only [h0, h3, h57, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h0, h1, h51, h52, h60, hc15, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h3, h51, h55, h63, hc13, hlam, hphi, ht01, u0ehi8]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                            · linarith only [h0, h1, h63, h66, hc12, hc23, hlam, hphi]
                            · linarith only [h3, h51, h66, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                          · linarith only [h3, h51, h65, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · linarith only [h54, h55, h62, hc13, hc35, hlam, hphi]
                  · linarith only [h3, h51, h59, hc12, hc23, hlam, hphi]
            · linarith only [h3, h51, h54, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
          · linarith only [h0, h73, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
            · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
              · linarith only [h76, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                · linarith only [h0, h1, h3, h78, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                  · linarith only [h0, h1, h51, h80, hc15, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h0, h1, h73, h82, hc15, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h76, h85, hc13, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                            · linarith only [h0, h1, h85, h88, hc12, hc23, hlam, hphi]
                            · linarith only [h3, h88, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h3, h75, h87, hlam, hphi, u0ehi6, u0elo2]
                      · linarith only [h75, h76, h84, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
              · linarith only [h93, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                · linarith only [h3, h95, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h0, h51, h97, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h0, h1, h99, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                      · linarith only [h101, h75, hc13, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                        · linarith only [h101, h103, h3, h93, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                          · linarith only [h105, h3, h75, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                          · linarith only [h105, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h108 | h108
    · linarith only [h108, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h110 | h110
      · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
        · rcases m.htr 0 2 5 (by decide) (by decide) with h112 | h112
          · linarith only [h112, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
            · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
              · linarith only [h115, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h0, h112, h119, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h119, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h111, h118, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h110, h112, h117, hc25, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h124, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                    · linarith only [h112, h128, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h128, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h111, h127, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h110, h112, h126, hc25, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h133 | h133
          · linarith only [h133, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h135 | h135
            · linarith only [h110, h111, h135, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
              · linarith only [h110, h111, h137, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                  · linarith only [h111, h140, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h140, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h110, h139, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h144 | h144
        · rcases m.htr 0 2 5 (by decide) (by decide) with h145 | h145
          · linarith only [h110, h145, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h147 | h147
            · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
              · linarith only [h148, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                · linarith only [h110, h150, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h150, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h110, h144, h147, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
          · linarith only [h154, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
            · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
              · linarith only [h157, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                · linarith only [h110, h159, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h159, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
              · linarith only [h162, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                · linarith only [h0, h110, h164, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h164, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sBT1_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · linarith only [h0, h1, hc15, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h6, h8, hc12, hlam, hphi, u1ehi0]
        · linarith only [h0, h8, hc25, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sBT1_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h1elo := hb1.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo4, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h12 | h12
    · linarith only [h12, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h12, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h16 | h16
    · linarith only [h16, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h16, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h19 | h19
    · linarith only [h19, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · linarith only [h19, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h23 | h23
    · linarith only [h23, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h23, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h26 | h26
    · linarith only [h26, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
    · linarith only [h26, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h30 | h30
    · linarith only [h30, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
    · linarith only [h30, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
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
    · linarith only [h34, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h34, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h37 | h37
    · linarith only [h37, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
    · linarith only [h37, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h40 | h40
    · linarith only [h40, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5ehi := hb5.2.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h12, h3, h8, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h0, h11, h12, h4, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h0, h11, h4, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                  · linarith only [h0, h4, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h1, h21, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h0, h20, h21, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h20, h4, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
                  · linarith only [h0, h17, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · linarith only [h26, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h29, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                        · linarith only [h1, h32, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h26, h34, hc14, hlam, hphi, ht01, u0ehi8]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                            · linarith only [h28, h29, h3, h36, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h36, h5, h6, hc23, hc35, hlam, hphi]
                      · linarith only [h31, h5, h6, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h28, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h41 | h41
              · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h0, h44, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                      · linarith only [h41, h46, h5, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                        · linarith only [h3, h43, h44, h48, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h41, h48, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi2]
                  · linarith only [h0, h4, h43, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · linarith only [h41, h42, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h0, h55, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                      · linarith only [h1, h5, h57, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                        · linarith only [h3, h41, h54, h55, h59, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                          · linarith only [h2, h61, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h2, h53, h61, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                  · linarith only [h0, h4, h54, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                    · linarith only [h0, h66, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                      · linarith only [h5, h68, hc13, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
                        · linarith only [h3, h41, h65, h66, h70, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h3, h53, h65, h66, h72, hc14, hlam, hphi, u0ehi8, u0elo0, u1ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                            · linarith only [h3, h5, h65, h66, h74, hlam, hphi, u0ehi7, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h3, h41, h65, h66, h76, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h3, h5, h53, h65, h66, h78, hc34, hlam, hphi, ht12, ht23, u0ehi7, u0elo0, u1ehi2]
                                · linarith only [h3, h5, h65, h66, h78, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi7, u0elo0, u1ehi2]
                  · linarith only [h0, h4, h65, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h82 | h82
            · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
              · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
                · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                  · linarith only [h4, h85, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                    · linarith only [h1, h85, h87, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                        · linarith only [h1, h90, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h83, h85, h90, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
                      · linarith only [h1, h82, h85, h89, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                  · linarith only [h4, h94, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h1, h94, h96, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                        · linarith only [h1, h99, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h1, h83, h94, h99, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                      · linarith only [h1, h82, h94, h98, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                · linarith only [h103, h82, h83, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                  · linarith only [h105, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                    · linarith only [h1, h105, h107, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                        · linarith only [h1, h110, h83, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                          · linarith only [h103, h105, h110, h112, h3, hc14, hlam, hphi, u0ehi8, u0elo0, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                              · linarith only [h105, h110, h115, h3, h82, h83, hc23, hlam, hphi, ht12, u0ehi8, u0elo0, u1ehi1]
                              · linarith only [h105, h110, h115, h3, h4, hc35, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h109, h110, h114, h3, h4, hlam, hphi, u0ehi6, u0elo0]
                      · linarith only [h105, h109, h82, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                  · linarith only [h122, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                    · linarith only [h1, h122, h124, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h1, h126, h82, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                        · linarith only [h126, h128, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h120, h122, h128, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
                · linarith only [h120, h121, h82, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                  · linarith only [h133, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                    · linarith only [h1, h133, h135, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h137 | h137
                      · linarith only [h1, h137, h4, h82, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
                        · linarith only [h120, h137, h139, h2, h4, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                          · linarith only [h141, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h132, h133, h137, h141, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                  · linarith only [h144, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                    · linarith only [h1, h144, h146, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                      · linarith only [h1, h148, h82, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h150 | h150
                        · linarith only [h120, h148, h150, h2, h4, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                          · linarith only [h132, h152, h2, h4, h82, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                            · linarith only [h144, h148, h152, h154, h3, h4, h82, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h144, h148, h152, h154, h3, h4, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h1, h2, hc14, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h160 | h160
    · linarith only [h0, h160, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h162 | h162
      · linarith only [h0, h162, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h164 | h164
        · linarith only [h0, h164, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h166 | h166
          · rcases m.htr 0 3 4 (by decide) (by decide) with h167 | h167
            · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
              · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
                · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                              · linarith only [h166, h176, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h166, h168, h175, h176, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                              · linarith only [h166, h179, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                                · linarith only [h166, h167, h181, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                · linarith only [h166, h167, h169, h175, h181, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h166, h167, h169, h174, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                        · linarith only [h162, h172, h173, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h160, h172, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h171, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h170, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h169, h189, h191, h193, hc12, hlam, hphi, ht01, u0ehi8]
                          · linarith only [h162, h193, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                        · linarith only [h166, h168, h192, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                      · linarith only [h160, h166, h167, h191, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h0, h190, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h166, h189, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h200 | h200
                · linarith only [h167, h168, h200, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h204 | h204
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h205 | h205
                        · linarith only [h168, h202, h205, hc12, hlam, hphi, ht01, u0ehi7]
                        · linarith only [h160, h205, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h160, h204, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h203, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h166, h202, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
              · rcases m.htr 0 4 5 (by decide) (by decide) with h212 | h212
                · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                      · linarith only [h167, h211, h213, h215, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h160, h215, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h214, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h166, h213, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h167, h211, h212, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                      · linarith only [h167, h222, h224, hc12, hlam, hphi, ht01, u0ehi7]
                      · linarith only [h160, h224, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h223, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h166, h222, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
                      · linarith only [h160, h167, h229, h231, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h160, h231, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h230, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h166, h229, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h236 | h236
            · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
              · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                  · linarith only [h166, h239, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h239, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h166, h242, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h242, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
                · linarith only [h236, h237, h245, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                  · linarith only [h0, h166, h247, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h247, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
              · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
                · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
                  · linarith only [h0, h166, h252, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h252, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h236, h250, h251, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
                · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                  · linarith only [h0, h166, h257, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h257, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                  · linarith only [h0, h166, h260, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h260, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sBT1_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1elo := hb1.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht01, p0_1, u0ehi9, u1elo4]
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

theorem n7l_sBT1_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h1ehi := hb1.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo3]
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo4]
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

theorem n7l_sBT1_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1elo := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
              · linarith only [h1, h10, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
              · linarith only [h10, h9, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
              · linarith only [h1, h13, h2, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h1, h18, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                      · linarith only [h18, h3, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h15, h17, h3, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h15, h16, h3, h9, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h15, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
          · linarith only [h0, h25, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
          · linarith only [h24, h25, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
          · linarith only [h0, h28, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
            · linarith only [h1, h2, h30, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
              · linarith only [h1, h32, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                · linarith only [h2, h34, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h24, h32, h34, h36, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h24, h36, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h1, hlam, hphi, ht01, u0ehi5, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sBT1_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
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
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h7, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h10 | h10
            · linarith only [h10, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h10, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 1 5) (by simp) with h14 | h14
            · linarith only [h14, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h14, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h17 | h17
            · linarith only [h17, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h17, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 2) (by simp) with h22 | h22
      · rcases p0_3 (m.d 1 3) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 1 5) (by simp) with h26 | h26
            · linarith only [h26, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h26, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h29 | h29
            · linarith only [h29, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 1 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h35, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
            · linarith only [h38, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h38, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 2) (by simp) with h43 | h43
      · rcases p0_3 (m.d 1 3) (by simp) with h44 | h44
        · rcases p0_3 (m.d 1 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h47 | h47
            · linarith only [h47, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · linarith only [h47, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h52, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
      · rcases p0_3 (m.d 1 3) (by simp) with h55 | h55
        · rcases p0_3 (m.d 1 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h58, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h63 | h63
            · linarith only [h55, h63, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h63, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 2) (by simp) with h71 | h71
      · rcases p0_3 (m.d 1 3) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 1 5) (by simp) with h75 | h75
            · linarith only [h75, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h70, h75, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h78 | h78
            · linarith only [h78, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h70, h78, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc12, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 2) (by simp) with h84 | h84
      · rcases p0_3 (m.d 1 3) (by simp) with h85 | h85
        · rcases p0_3 (m.d 1 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h88 | h88
            · linarith only [h88, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · linarith only [h83, h88, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · rcases p0_3 (m.d 1 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h83, h93, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc12, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h98 | h98
    · linarith only [h98, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
    · linarith only [h98, hc12, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h102 | h102
    · rcases p0_3 (m.d 1 2) (by simp) with h103 | h103
      · linarith only [h103, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h105 | h105
        · rcases p0_3 (m.d 1 4) (by simp) with h106 | h106
          · rcases p0_3 (m.d 1 5) (by simp) with h107 | h107
            · linarith only [h107, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h102, h107, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · rcases p0_3 (m.d 1 5) (by simp) with h110 | h110
            · linarith only [h110, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h102, h110, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · linarith only [h105, hlam, p0_0]
    · linarith only [h102, hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h116 | h116
    · rcases p0_3 (m.d 1 2) (by simp) with h117 | h117
      · rcases p0_3 (m.d 1 3) (by simp) with h118 | h118
        · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h121 | h121
            · linarith only [h121, hc14, hlam, hphi, ht45, p0_1, u5elo1]
            · linarith only [h116, h121, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · linarith only [h118, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h125 | h125
        · rcases p0_3 (m.d 1 4) (by simp) with h126 | h126
          · linarith only [h126, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h128 | h128
            · linarith only [h117, h128, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h116, h128, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
        · linarith only [h125, hlam, p0_0]
    · linarith only [h116, hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h133 | h133
    · linarith only [h133, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
    · linarith only [h133, hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h137 | h137
    · rcases p0_3 (m.d 1 2) (by simp) with h138 | h138
      · linarith only [h138, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h140 | h140
        · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 1 5) (by simp) with h142 | h142
            · linarith only [h142, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h137, h142, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 1 5) (by simp) with h147 | h147
            · linarith only [h147, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h137, h147, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · linarith only [h146, hlam, p0_0]
    · linarith only [h137, hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h152 | h152
    · rcases p0_3 (m.d 1 2) (by simp) with h153 | h153
      · rcases p0_3 (m.d 1 3) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 1 5) (by simp) with h157 | h157
            · linarith only [h157, hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
            · linarith only [h152, h157, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h161 | h161
        · linarith only [h161, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 1 5) (by simp) with h164 | h164
            · linarith only [h153, h164, hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
            · linarith only [h152, h164, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
          · linarith only [h163, hlam, p0_0]
    · linarith only [h152, hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h170 | h170
    · linarith only [h170, hlam, hphi, ht0b, ht5b, p0_1, u0elo0, u5ehi6]
    · linarith only [h170, hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht34, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT1_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hc13, hlam, hphi, u1ehi4]
    · linarith only [h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

end R2N4
