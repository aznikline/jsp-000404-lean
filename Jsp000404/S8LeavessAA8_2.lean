import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n8l_sAA8_H_I_H_L (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u1elo5 := h1elo (m.d 1 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 1 6 (by decide) (by decide) with h4 | h4
          · rcases h0emin with h5 | h5 | h5 | h5 | h5 | h5
            · linarith only [h5, hlam, ht01, u1elo0]
            · linarith only [h0, h5, hlam, ht01, u1elo0]
            · linarith only [h1, h5, hlam, ht01, u1elo0]
            · linarith only [h2, h5, hlam, ht01, u1elo0]
            · linarith only [h3, h5, hlam, ht01, u1elo0]
            · linarith only [h4, h5, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo5]
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n8l_sAA8_H_I_H_R (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0emax := hb0.2.2
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 1 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 1 6 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 5 6 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 5 6 (by decide) (by decide) with h9 | h9
                    · rcases h0emax with h10 | h10 | h10 | h10 | h10 | h10
                      · linarith only [h0, h10, h6, h7, h8, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                      · linarith only [h0, h10, h6, h7, h8, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                      · linarith only [h1, h10, h7, h8, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                      · linarith only [h10, h2, h8, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                      · linarith only [h10, h3, h9, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                      · linarith only [h10, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                    · linarith only [h9, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4]
                  · linarith only [h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                · linarith only [h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · linarith only [h6, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h3, h5, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4]
          · linarith only [h4, hc16, hlam, hphi, u1ehi0]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

set_option maxHeartbeats 3254000 in
theorem n8l_sAA8_H_I_M_IR (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 1 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 0 6) (by simp) with h8 | h8
              · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
                · linarith only [h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h9, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
                · linarith only [h12, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h12, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
              · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
                · linarith only [h16, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h16, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
                · linarith only [h19, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h19, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 0 6) (by simp) with h23 | h23
              · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
                · linarith only [h24, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h24, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
                · linarith only [h27, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h27, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h30 | h30
              · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
                · linarith only [h31, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h31, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h34 | h34
                · linarith only [h34, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h34, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h37 | h37
          · rcases p0_3 (m.d 0 5) (by simp) with h38 | h38
            · rcases p0_3 (m.d 0 6) (by simp) with h39 | h39
              · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
                · linarith only [h40, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h40, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
                · linarith only [h43, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h43, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h46 | h46
              · rcases m.htr 0 1 2 (by decide) (by decide) with h47 | h47
                · linarith only [h47, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h47, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h50 | h50
                · linarith only [h50, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases p0_3 (m.d 0 6) (by simp) with h54 | h54
              · rcases m.htr 0 1 2 (by decide) (by decide) with h55 | h55
                · linarith only [h55, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h55, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
                · linarith only [h58, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h58, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h61 | h61
              · rcases m.htr 0 1 2 (by decide) (by decide) with h62 | h62
                · linarith only [h62, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h62, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h65 | h65
                · linarith only [h65, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h65, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h69 | h69
    · rcases p0_3 (m.d 0 2) (by simp) with h70 | h70
      · rcases p0_3 (m.d 0 3) (by simp) with h71 | h71
        · linarith only [h71, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h73 | h73
          · rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
            · rcases p0_3 (m.d 0 6) (by simp) with h75 | h75
              · rcases m.htr 0 1 2 (by decide) (by decide) with h76 | h76
                · linarith only [h70, h76, hlam]
                · linarith only [h76, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h79 | h79
                · linarith only [h70, h79, hlam]
                · linarith only [h79, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h82 | h82
              · rcases m.htr 0 1 2 (by decide) (by decide) with h83 | h83
                · linarith only [h70, h83, hlam]
                · linarith only [h83, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h86 | h86
                · linarith only [h70, h86, hlam]
                · linarith only [h86, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h89 | h89
            · rcases p0_3 (m.d 0 6) (by simp) with h90 | h90
              · rcases m.htr 0 1 2 (by decide) (by decide) with h91 | h91
                · linarith only [h70, h91, hlam]
                · linarith only [h91, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h94 | h94
                · linarith only [h70, h94, hlam]
                · linarith only [h94, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h97 | h97
              · rcases m.htr 0 1 2 (by decide) (by decide) with h98 | h98
                · linarith only [h70, h98, hlam]
                · linarith only [h98, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h70, hlam]
                · linarith only [h101, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h104 | h104
        · linarith only [h104, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h106 | h106
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 0 6) (by simp) with h108 | h108
              · rcases m.htr 0 1 2 (by decide) (by decide) with h109 | h109
                · linarith only [h109, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h109, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
                · linarith only [h112, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h112, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h115 | h115
              · rcases m.htr 0 1 2 (by decide) (by decide) with h116 | h116
                · linarith only [h116, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h116, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h119 | h119
                · linarith only [h119, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h119, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h122 | h122
            · rcases p0_3 (m.d 0 6) (by simp) with h123 | h123
              · rcases m.htr 0 1 2 (by decide) (by decide) with h124 | h124
                · linarith only [h124, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h124, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h127 | h127
                · linarith only [h127, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h127, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h130 | h130
              · rcases m.htr 0 1 2 (by decide) (by decide) with h131 | h131
                · linarith only [h131, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h131, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h134 | h134
                · linarith only [h134, h70, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h134, h70, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h69, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h138 | h138
    · rcases p0_3 (m.d 0 2) (by simp) with h139 | h139
      · rcases p0_3 (m.d 0 3) (by simp) with h140 | h140
        · rcases p0_3 (m.d 0 4) (by simp) with h141 | h141
          · linarith only [h141, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h143 | h143
            · rcases p0_3 (m.d 0 6) (by simp) with h144 | h144
              · rcases m.htr 0 1 2 (by decide) (by decide) with h145 | h145
                · linarith only [h139, h145, hlam]
                · linarith only [h145, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h148 | h148
                · linarith only [h139, h148, hlam]
                · linarith only [h148, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h151 | h151
              · rcases m.htr 0 1 2 (by decide) (by decide) with h152 | h152
                · linarith only [h139, h152, hlam]
                · linarith only [h152, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h155 | h155
                · linarith only [h139, h155, hlam]
                · linarith only [h155, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h158 | h158
          · linarith only [h158, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · rcases p0_3 (m.d 0 6) (by simp) with h161 | h161
              · rcases m.htr 0 1 2 (by decide) (by decide) with h162 | h162
                · linarith only [h139, h162, hlam]
                · linarith only [h140, h162, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h165 | h165
                · linarith only [h139, h165, hlam]
                · linarith only [h140, h165, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h168 | h168
              · rcases m.htr 0 1 2 (by decide) (by decide) with h169 | h169
                · linarith only [h139, h169, hlam]
                · linarith only [h140, h169, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h172 | h172
                · linarith only [h139, h172, hlam]
                · linarith only [h140, h172, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h175 | h175
        · rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
          · linarith only [h176, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h178 | h178
            · rcases p0_3 (m.d 0 6) (by simp) with h179 | h179
              · rcases m.htr 0 1 2 (by decide) (by decide) with h180 | h180
                · linarith only [h139, h180, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h180, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h183 | h183
                · linarith only [h139, h183, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h183, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h186 | h186
              · rcases m.htr 0 1 2 (by decide) (by decide) with h187 | h187
                · linarith only [h139, h187, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h187, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h190 | h190
                · linarith only [h139, h190, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h190, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h193 | h193
          · linarith only [h193, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h195 | h195
            · rcases p0_3 (m.d 0 6) (by simp) with h196 | h196
              · rcases m.htr 0 1 2 (by decide) (by decide) with h197 | h197
                · linarith only [h139, h197, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h197, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h200 | h200
                · linarith only [h139, h200, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h200, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h203 | h203
              · rcases m.htr 0 1 2 (by decide) (by decide) with h204 | h204
                · linarith only [h139, h204, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h204, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h207 | h207
                · linarith only [h139, h207, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h139, h207, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h138, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h211 | h211
    · rcases p0_3 (m.d 0 2) (by simp) with h212 | h212
      · rcases p0_3 (m.d 0 3) (by simp) with h213 | h213
        · rcases p0_3 (m.d 0 4) (by simp) with h214 | h214
          · rcases p0_3 (m.d 0 5) (by simp) with h215 | h215
            · linarith only [h215, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h217 | h217
              · rcases m.htr 0 1 2 (by decide) (by decide) with h218 | h218
                · linarith only [h212, h218, hlam]
                · linarith only [h218, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h221 | h221
                · linarith only [h212, h221, hlam]
                · linarith only [h221, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h224 | h224
            · linarith only [h224, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h226 | h226
              · rcases m.htr 0 1 2 (by decide) (by decide) with h227 | h227
                · linarith only [h212, h227, hlam]
                · linarith only [h214, h227, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h230 | h230
                · linarith only [h212, h230, hlam]
                · linarith only [h214, h230, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h233 | h233
          · rcases p0_3 (m.d 0 5) (by simp) with h234 | h234
            · linarith only [h234, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h236 | h236
              · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
                · linarith only [h212, h237, hlam]
                · linarith only [h213, h237, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h240 | h240
                · linarith only [h212, h240, hlam]
                · linarith only [h213, h240, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h243 | h243
            · linarith only [h243, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h245 | h245
              · rcases m.htr 0 1 2 (by decide) (by decide) with h246 | h246
                · linarith only [h212, h246, hlam]
                · linarith only [h213, h246, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h249 | h249
                · linarith only [h212, h249, hlam]
                · linarith only [h213, h249, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h252 | h252
        · rcases p0_3 (m.d 0 4) (by simp) with h253 | h253
          · rcases p0_3 (m.d 0 5) (by simp) with h254 | h254
            · linarith only [h254, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h256 | h256
              · rcases m.htr 0 1 2 (by decide) (by decide) with h257 | h257
                · linarith only [h212, h257, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h257, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h260 | h260
                · linarith only [h212, h260, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h260, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h263 | h263
            · linarith only [h263, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h265 | h265
              · rcases m.htr 0 1 2 (by decide) (by decide) with h266 | h266
                · linarith only [h212, h266, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h266, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h269 | h269
                · linarith only [h212, h269, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h269, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 0 5) (by simp) with h273 | h273
            · linarith only [h273, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h275 | h275
              · rcases m.htr 0 1 2 (by decide) (by decide) with h276 | h276
                · linarith only [h212, h276, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h276, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h279 | h279
                · linarith only [h212, h279, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h279, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h282 | h282
            · linarith only [h282, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h284 | h284
              · rcases m.htr 0 1 2 (by decide) (by decide) with h285 | h285
                · linarith only [h212, h285, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h285, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h288 | h288
                · linarith only [h212, h288, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h212, h288, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h211, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h292 | h292
    · rcases p0_3 (m.d 0 2) (by simp) with h293 | h293
      · rcases p0_3 (m.d 0 3) (by simp) with h294 | h294
        · rcases p0_3 (m.d 0 4) (by simp) with h295 | h295
          · rcases p0_3 (m.d 0 5) (by simp) with h296 | h296
            · rcases p0_3 (m.d 0 6) (by simp) with h297 | h297
              · linarith only [h297, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h299 | h299
                · linarith only [h293, h299, hlam]
                · linarith only [h299, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h302 | h302
              · linarith only [h302, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h304 | h304
                · linarith only [h293, h304, hlam]
                · linarith only [h296, h304, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h307 | h307
            · rcases p0_3 (m.d 0 6) (by simp) with h308 | h308
              · linarith only [h308, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h310 | h310
                · linarith only [h293, h310, hlam]
                · linarith only [h295, h310, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h313 | h313
              · linarith only [h313, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h315 | h315
                · linarith only [h293, h315, hlam]
                · linarith only [h295, h315, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h318 | h318
          · rcases p0_3 (m.d 0 5) (by simp) with h319 | h319
            · rcases p0_3 (m.d 0 6) (by simp) with h320 | h320
              · linarith only [h320, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h322 | h322
                · linarith only [h293, h322, hlam]
                · linarith only [h294, h322, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h325 | h325
              · linarith only [h325, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h327 | h327
                · linarith only [h293, h327, hlam]
                · linarith only [h294, h327, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h330 | h330
            · rcases p0_3 (m.d 0 6) (by simp) with h331 | h331
              · linarith only [h331, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h333 | h333
                · linarith only [h293, h333, hlam]
                · linarith only [h294, h333, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h336 | h336
              · linarith only [h336, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h338 | h338
                · linarith only [h293, h338, hlam]
                · linarith only [h294, h338, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h341 | h341
        · rcases p0_3 (m.d 0 4) (by simp) with h342 | h342
          · rcases p0_3 (m.d 0 5) (by simp) with h343 | h343
            · rcases p0_3 (m.d 0 6) (by simp) with h344 | h344
              · linarith only [h344, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h346 | h346
                · linarith only [h293, h346, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h346, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h349 | h349
              · linarith only [h349, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h351 | h351
                · linarith only [h293, h351, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h351, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h354 | h354
            · rcases p0_3 (m.d 0 6) (by simp) with h355 | h355
              · linarith only [h355, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
                · linarith only [h293, h357, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h357, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h360 | h360
              · linarith only [h360, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h362 | h362
                · linarith only [h293, h362, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h362, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h365 | h365
          · rcases p0_3 (m.d 0 5) (by simp) with h366 | h366
            · rcases p0_3 (m.d 0 6) (by simp) with h367 | h367
              · linarith only [h367, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h369 | h369
                · linarith only [h293, h369, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h369, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h372 | h372
              · linarith only [h372, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h374 | h374
                · linarith only [h293, h374, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h374, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 0 6) (by simp) with h378 | h378
              · linarith only [h378, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h380 | h380
                · linarith only [h293, h380, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h380, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h383 | h383
              · linarith only [h383, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h385 | h385
                · linarith only [h293, h385, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h293, h385, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
    · linarith only [h292, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h391 | h391
    · rcases p0_3 (m.d 0 2) (by simp) with h392 | h392
      · rcases p0_3 (m.d 0 3) (by simp) with h393 | h393
        · linarith only [h393, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h395 | h395
          · rcases p0_3 (m.d 0 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 0 6) (by simp) with h397 | h397
              · rcases m.htr 0 1 2 (by decide) (by decide) with h398 | h398
                · rcases m.htr 0 1 3 (by decide) (by decide) with h399 | h399
                  · linarith only [h398, h399, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h398, h399, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h398, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h403 | h403
                · rcases m.htr 0 1 3 (by decide) (by decide) with h404 | h404
                  · linarith only [h403, h404, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h403, h404, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h403, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h408 | h408
              · rcases m.htr 0 1 2 (by decide) (by decide) with h409 | h409
                · rcases m.htr 0 1 3 (by decide) (by decide) with h410 | h410
                  · linarith only [h409, h410, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h409, h410, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h409, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h414 | h414
                · rcases m.htr 0 1 3 (by decide) (by decide) with h415 | h415
                  · linarith only [h414, h415, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h414, h415, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h414, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h419 | h419
            · rcases p0_3 (m.d 0 6) (by simp) with h420 | h420
              · rcases m.htr 0 1 2 (by decide) (by decide) with h421 | h421
                · rcases m.htr 0 1 3 (by decide) (by decide) with h422 | h422
                  · linarith only [h421, h422, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h421, h422, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h421, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h426 | h426
                · rcases m.htr 0 1 3 (by decide) (by decide) with h427 | h427
                  · linarith only [h426, h427, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h426, h427, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h426, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h431 | h431
              · rcases m.htr 0 1 2 (by decide) (by decide) with h432 | h432
                · rcases m.htr 0 1 3 (by decide) (by decide) with h433 | h433
                  · linarith only [h432, h433, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h432, h433, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h432, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h437 | h437
                · rcases m.htr 0 1 3 (by decide) (by decide) with h438 | h438
                  · linarith only [h437, h438, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h437, h438, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h391, h437, hlam]
      · linarith only [h392, hlam, p0_0]
    · linarith only [h391, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h444 | h444
    · rcases p0_3 (m.d 0 2) (by simp) with h445 | h445
      · rcases p0_3 (m.d 0 3) (by simp) with h446 | h446
        · rcases p0_3 (m.d 0 4) (by simp) with h447 | h447
          · linarith only [h447, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h449 | h449
            · rcases p0_3 (m.d 0 6) (by simp) with h450 | h450
              · rcases m.htr 0 1 2 (by decide) (by decide) with h451 | h451
                · rcases m.htr 0 1 3 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h453 | h453
                    · linarith only [h451, h453, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h451, h453, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h451, h452, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h451, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h458 | h458
                · rcases m.htr 0 1 3 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h460 | h460
                    · linarith only [h458, h460, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h458, h460, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h458, h459, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h458, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h465 | h465
              · rcases m.htr 0 1 2 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 1 3 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h468 | h468
                    · linarith only [h466, h468, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h466, h468, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h466, h467, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h466, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h473 | h473
                · rcases m.htr 0 1 3 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h475 | h475
                    · linarith only [h473, h475, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h473, h475, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h473, h474, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h473, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h480 | h480
          · linarith only [h480, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h482 | h482
            · rcases p0_3 (m.d 0 6) (by simp) with h483 | h483
              · rcases m.htr 0 1 2 (by decide) (by decide) with h484 | h484
                · rcases m.htr 0 1 3 (by decide) (by decide) with h485 | h485
                  · linarith only [h446, h484, h485, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h446, h484, h485, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h484, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
                · rcases m.htr 0 1 3 (by decide) (by decide) with h490 | h490
                  · linarith only [h446, h489, h490, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h446, h489, h490, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h489, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h494 | h494
              · rcases m.htr 0 1 2 (by decide) (by decide) with h495 | h495
                · rcases m.htr 0 1 3 (by decide) (by decide) with h496 | h496
                  · linarith only [h446, h495, h496, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h446, h495, h496, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h495, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h500 | h500
                · rcases m.htr 0 1 3 (by decide) (by decide) with h501 | h501
                  · linarith only [h446, h500, h501, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h446, h500, h501, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h444, h500, hlam]
      · linarith only [h445, hlam, p0_0]
    · linarith only [h444, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h507 | h507
    · rcases p0_3 (m.d 0 2) (by simp) with h508 | h508
      · rcases p0_3 (m.d 0 3) (by simp) with h509 | h509
        · rcases p0_3 (m.d 0 4) (by simp) with h510 | h510
          · rcases p0_3 (m.d 0 5) (by simp) with h511 | h511
            · linarith only [h511, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h513 | h513
              · rcases m.htr 0 1 2 (by decide) (by decide) with h514 | h514
                · rcases m.htr 0 1 3 (by decide) (by decide) with h515 | h515
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h516 | h516
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h517 | h517
                      · linarith only [h514, h517, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h514, h517, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h514, h516, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h514, h515, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h507, h514, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h523 | h523
                · rcases m.htr 0 1 3 (by decide) (by decide) with h524 | h524
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h525 | h525
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h526 | h526
                      · linarith only [h523, h526, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h523, h526, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h523, h525, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h523, h524, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h507, h523, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h532 | h532
            · linarith only [h532, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h534 | h534
              · rcases m.htr 0 1 2 (by decide) (by decide) with h535 | h535
                · rcases m.htr 0 1 3 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h537 | h537
                    · linarith only [h510, h535, h537, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h510, h535, h537, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h510, h535, h536, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h507, h535, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h542 | h542
                · rcases m.htr 0 1 3 (by decide) (by decide) with h543 | h543
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h544 | h544
                    · linarith only [h510, h542, h544, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h510, h542, h544, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h510, h542, h543, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h507, h542, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h549 | h549
          · rcases p0_3 (m.d 0 5) (by simp) with h550 | h550
            · linarith only [h550, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h552 | h552
              · rcases m.htr 0 1 2 (by decide) (by decide) with h553 | h553
                · rcases m.htr 0 1 3 (by decide) (by decide) with h554 | h554
                  · linarith only [h509, h553, h554, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h509, h553, h554, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h507, h553, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h558 | h558
                · rcases m.htr 0 1 3 (by decide) (by decide) with h559 | h559
                  · linarith only [h509, h558, h559, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h509, h558, h559, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h507, h558, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h563 | h563
            · linarith only [h563, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h565 | h565
              · rcases m.htr 0 1 2 (by decide) (by decide) with h566 | h566
                · rcases m.htr 0 1 3 (by decide) (by decide) with h567 | h567
                  · linarith only [h509, h566, h567, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h509, h566, h567, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h507, h566, hlam]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h571 | h571
                · rcases m.htr 0 1 3 (by decide) (by decide) with h572 | h572
                  · linarith only [h509, h571, h572, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h509, h571, h572, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h507, h571, hlam]
      · linarith only [h508, hlam, p0_0]
    · linarith only [h507, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h578 | h578
    · rcases p0_3 (m.d 0 2) (by simp) with h579 | h579
      · rcases p0_3 (m.d 0 3) (by simp) with h580 | h580
        · rcases p0_3 (m.d 0 4) (by simp) with h581 | h581
          · rcases p0_3 (m.d 0 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 0 6) (by simp) with h583 | h583
              · linarith only [h583, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 1 3 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h587 | h587
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h589 | h589
                        · linarith only [h585, h589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                        · linarith only [h585, h589, hc06, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                      · linarith only [h585, h588, hc06, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h585, h587, hc06, hc14, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                  · linarith only [h585, h586, hc06, hc13, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                · linarith only [h578, h585, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h596 | h596
              · linarith only [h596, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h598 | h598
                · rcases m.htr 0 1 3 (by decide) (by decide) with h599 | h599
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h600 | h600
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h601 | h601
                      · linarith only [h582, h598, h601, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h582, h598, h601, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h582, h598, h600, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h582, h598, h599, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h578, h598, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h607 | h607
            · rcases p0_3 (m.d 0 6) (by simp) with h608 | h608
              · linarith only [h608, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h610 | h610
                · rcases m.htr 0 1 3 (by decide) (by decide) with h611 | h611
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h612 | h612
                    · linarith only [h581, h610, h612, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h581, h610, h612, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h581, h610, h611, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h578, h610, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h617 | h617
              · linarith only [h617, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h619 | h619
                · rcases m.htr 0 1 3 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h621 | h621
                    · linarith only [h581, h619, h621, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h581, h619, h621, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h581, h619, h620, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h578, h619, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h626 | h626
          · rcases p0_3 (m.d 0 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 0 6) (by simp) with h628 | h628
              · linarith only [h628, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h630 | h630
                · rcases m.htr 0 1 3 (by decide) (by decide) with h631 | h631
                  · linarith only [h580, h630, h631, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h580, h630, h631, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h578, h630, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h635 | h635
              · linarith only [h635, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h637 | h637
                · rcases m.htr 0 1 3 (by decide) (by decide) with h638 | h638
                  · linarith only [h580, h637, h638, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h580, h637, h638, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h578, h637, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h642 | h642
            · rcases p0_3 (m.d 0 6) (by simp) with h643 | h643
              · linarith only [h643, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h645 | h645
                · rcases m.htr 0 1 3 (by decide) (by decide) with h646 | h646
                  · linarith only [h580, h645, h646, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h580, h645, h646, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h578, h645, hlam]
            · rcases p0_3 (m.d 0 6) (by simp) with h650 | h650
              · linarith only [h650, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h652 | h652
                · rcases m.htr 0 1 3 (by decide) (by decide) with h653 | h653
                  · linarith only [h580, h652, h653, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h580, h652, h653, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h578, h652, hlam]
      · linarith only [h579, hlam, p0_0]
    · linarith only [h578, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h660 | h660
    · rcases p0_3 (m.d 0 2) (by simp) with h661 | h661
      · linarith only [h661, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h663 | h663
        · rcases p0_3 (m.d 0 4) (by simp) with h664 | h664
          · rcases p0_3 (m.d 0 5) (by simp) with h665 | h665
            · rcases p0_3 (m.d 0 6) (by simp) with h666 | h666
              · rcases m.htr 0 1 2 (by decide) (by decide) with h667 | h667
                · linarith only [h667, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h667, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h670 | h670
                · linarith only [h670, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h670, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h673 | h673
              · rcases m.htr 0 1 2 (by decide) (by decide) with h674 | h674
                · linarith only [h660, h674, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h674, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h677 | h677
                · linarith only [h660, h677, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h677, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h680 | h680
            · rcases p0_3 (m.d 0 6) (by simp) with h681 | h681
              · rcases m.htr 0 1 2 (by decide) (by decide) with h682 | h682
                · linarith only [h660, h682, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h682, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h685 | h685
                · linarith only [h685, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h685, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h688 | h688
              · rcases m.htr 0 1 2 (by decide) (by decide) with h689 | h689
                · linarith only [h660, h689, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h689, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h692 | h692
                · linarith only [h660, h692, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h660, h692, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h663, hlam, p0_0]
    · linarith only [h660, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h698 | h698
    · rcases p0_3 (m.d 0 2) (by simp) with h699 | h699
      · rcases p0_3 (m.d 0 3) (by simp) with h700 | h700
        · rcases p0_3 (m.d 0 4) (by simp) with h701 | h701
          · linarith only [h701, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h703 | h703
            · rcases p0_3 (m.d 0 6) (by simp) with h704 | h704
              · rcases m.htr 0 1 2 (by decide) (by decide) with h705 | h705
                · rcases m.htr 0 1 3 (by decide) (by decide) with h706 | h706
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h707 | h707
                    · linarith only [h699, h705, h707, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h699, h705, h707, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h698, h706, hlam]
                · linarith only [h698, h705, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h712 | h712
                · rcases m.htr 0 1 3 (by decide) (by decide) with h713 | h713
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h714 | h714
                    · linarith only [h699, h712, h714, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h699, h712, h714, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h698, h713, hlam]
                · linarith only [h698, h712, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h719 | h719
              · rcases m.htr 0 1 2 (by decide) (by decide) with h720 | h720
                · rcases m.htr 0 1 3 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h722 | h722
                    · linarith only [h699, h720, h722, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h699, h720, h722, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h698, h721, hlam]
                · linarith only [h698, h720, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h727 | h727
                · rcases m.htr 0 1 3 (by decide) (by decide) with h728 | h728
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h729 | h729
                    · linarith only [h699, h727, h729, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h699, h727, h729, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h698, h728, hlam]
                · linarith only [h698, h727, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h700, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h735 | h735
        · rcases p0_3 (m.d 0 4) (by simp) with h736 | h736
          · linarith only [h736, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h738 | h738
            · rcases p0_3 (m.d 0 6) (by simp) with h739 | h739
              · rcases m.htr 0 1 2 (by decide) (by decide) with h740 | h740
                · linarith only [h699, h740, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h698, h699, h740, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h743 | h743
                · linarith only [h699, h743, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h698, h699, h743, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h746 | h746
              · rcases m.htr 0 1 2 (by decide) (by decide) with h747 | h747
                · linarith only [h698, h699, h747, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h698, h699, h747, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h750 | h750
                · linarith only [h698, h699, h750, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h698, h699, h750, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h735, hlam, p0_0]
    · linarith only [h698, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h755 | h755
    · rcases p0_3 (m.d 0 2) (by simp) with h756 | h756
      · rcases p0_3 (m.d 0 3) (by simp) with h757 | h757
        · rcases p0_3 (m.d 0 4) (by simp) with h758 | h758
          · rcases p0_3 (m.d 0 5) (by simp) with h759 | h759
            · linarith only [h759, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h761 | h761
              · rcases m.htr 0 1 2 (by decide) (by decide) with h762 | h762
                · rcases m.htr 0 1 3 (by decide) (by decide) with h763 | h763
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h764 | h764
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h765 | h765
                      · linarith only [h756, h762, h765, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h756, h762, h765, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h756, h762, h764, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h755, h763, hlam]
                · linarith only [h755, h762, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h771 | h771
                · rcases m.htr 0 1 3 (by decide) (by decide) with h772 | h772
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h773 | h773
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h774 | h774
                      · linarith only [h756, h774, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h772, h774, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h772, h773, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h755, h772, hlam]
                · linarith only [h755, h771, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h780 | h780
            · linarith only [h780, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h782 | h782
              · rcases m.htr 0 1 2 (by decide) (by decide) with h783 | h783
                · rcases m.htr 0 1 3 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h785 | h785
                    · linarith only [h756, h758, h785, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h758, h784, h785, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h755, h784, hlam]
                · linarith only [h755, h758, h783, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h790 | h790
                · rcases m.htr 0 1 3 (by decide) (by decide) with h791 | h791
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h792 | h792
                    · linarith only [h756, h758, h790, h792, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h756, h758, h790, h792, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h755, h791, hlam]
                · linarith only [h755, h758, h790, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h757, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h798 | h798
        · rcases p0_3 (m.d 0 4) (by simp) with h799 | h799
          · rcases p0_3 (m.d 0 5) (by simp) with h800 | h800
            · linarith only [h800, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h802 | h802
              · rcases m.htr 0 1 2 (by decide) (by decide) with h803 | h803
                · linarith only [h756, h803, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h755, h756, h803, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h806 | h806
                · linarith only [h756, h806, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h755, h756, h806, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h809 | h809
            · linarith only [h809, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h811 | h811
              · rcases m.htr 0 1 2 (by decide) (by decide) with h812 | h812
                · linarith only [h756, h812, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h755, h756, h812, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h815 | h815
                · linarith only [h756, h815, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h755, h756, h815, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h798, hlam, p0_0]
    · linarith only [h755, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h820 | h820
    · rcases p0_3 (m.d 0 2) (by simp) with h821 | h821
      · rcases p0_3 (m.d 0 3) (by simp) with h822 | h822
        · rcases p0_3 (m.d 0 4) (by simp) with h823 | h823
          · rcases p0_3 (m.d 0 5) (by simp) with h824 | h824
            · rcases p0_3 (m.d 0 6) (by simp) with h825 | h825
              · linarith only [h825, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h827 | h827
                · rcases m.htr 0 1 3 (by decide) (by decide) with h828 | h828
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h829 | h829
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h830 | h830
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h831 | h831
                        · linarith only [h821, h827, h831, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                        · linarith only [h821, h827, h831, hc06, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                      · linarith only [h821, h827, h830, hc06, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h821, h827, h829, hc06, hc14, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                  · linarith only [h820, h828, hlam]
                · linarith only [h820, h827, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h838 | h838
              · linarith only [h838, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h840 | h840
                · rcases m.htr 0 1 3 (by decide) (by decide) with h841 | h841
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h842 | h842
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h843 | h843
                      · linarith only [h821, h824, h843, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h824, h841, h843, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h824, h841, h842, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h820, h841, hlam]
                · linarith only [h820, h824, h840, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h849 | h849
            · rcases p0_3 (m.d 0 6) (by simp) with h850 | h850
              · linarith only [h850, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h852 | h852
                · rcases m.htr 0 1 3 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h854 | h854
                    · linarith only [h821, h823, h852, h854, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h821, h823, h852, h854, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h820, h853, hlam]
                · linarith only [h820, h823, h852, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h859 | h859
              · linarith only [h859, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h861 | h861
                · rcases m.htr 0 1 3 (by decide) (by decide) with h862 | h862
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h863 | h863
                    · linarith only [h821, h823, h863, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h823, h862, h863, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h820, h862, hlam]
                · linarith only [h820, h823, h861, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
        · linarith only [h822, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h869 | h869
        · rcases p0_3 (m.d 0 4) (by simp) with h870 | h870
          · rcases p0_3 (m.d 0 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 0 6) (by simp) with h872 | h872
              · linarith only [h872, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h874 | h874
                · linarith only [h820, h821, h874, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h820, h821, h874, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h877 | h877
              · linarith only [h877, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h879 | h879
                · linarith only [h821, h879, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h820, h821, h879, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h882 | h882
            · rcases p0_3 (m.d 0 6) (by simp) with h883 | h883
              · linarith only [h883, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h885 | h885
                · linarith only [h820, h821, h885, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h820, h821, h885, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h888 | h888
              · linarith only [h888, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h890 | h890
                · linarith only [h821, h890, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h820, h821, h890, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
        · linarith only [h869, hlam, p0_0]
    · linarith only [h820, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h896 | h896
    · rcases p0_3 (m.d 0 2) (by simp) with h897 | h897
      · linarith only [h897, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h899 | h899
        · rcases p0_3 (m.d 0 4) (by simp) with h900 | h900
          · rcases p0_3 (m.d 0 5) (by simp) with h901 | h901
            · rcases p0_3 (m.d 0 6) (by simp) with h902 | h902
              · rcases m.htr 0 1 2 (by decide) (by decide) with h903 | h903
                · linarith only [h903, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h903, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h906 | h906
                · linarith only [h906, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h906, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h909 | h909
              · rcases m.htr 0 1 2 (by decide) (by decide) with h910 | h910
                · linarith only [h896, h910, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h910, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h913 | h913
                · linarith only [h896, h913, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h913, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h900, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h917 | h917
          · rcases p0_3 (m.d 0 5) (by simp) with h918 | h918
            · rcases p0_3 (m.d 0 6) (by simp) with h919 | h919
              · rcases m.htr 0 1 2 (by decide) (by decide) with h920 | h920
                · linarith only [h896, h920, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h920, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h923 | h923
                · linarith only [h896, h923, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h923, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h926 | h926
              · rcases m.htr 0 1 2 (by decide) (by decide) with h927 | h927
                · linarith only [h896, h927, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h927, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h930 | h930
                · linarith only [h930, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h896, h930, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h917, hlam, p0_0]
    · linarith only [h896, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h935 | h935
    · rcases p0_3 (m.d 0 2) (by simp) with h936 | h936
      · rcases p0_3 (m.d 0 3) (by simp) with h937 | h937
        · linarith only [h937, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h939 | h939
          · rcases p0_3 (m.d 0 5) (by simp) with h940 | h940
            · rcases p0_3 (m.d 0 6) (by simp) with h941 | h941
              · rcases m.htr 0 1 2 (by decide) (by decide) with h942 | h942
                · rcases m.htr 0 1 3 (by decide) (by decide) with h943 | h943
                  · linarith only [h936, h942, h943, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h936, h942, h943, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h935, h942, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h947 | h947
                · rcases m.htr 0 1 3 (by decide) (by decide) with h948 | h948
                  · linarith only [h936, h947, h948, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h936, h947, h948, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h935, h947, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h952 | h952
              · rcases m.htr 0 1 2 (by decide) (by decide) with h953 | h953
                · rcases m.htr 0 1 3 (by decide) (by decide) with h954 | h954
                  · linarith only [h936, h953, h954, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h936, h953, h954, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h935, h953, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h958 | h958
                · rcases m.htr 0 1 3 (by decide) (by decide) with h959 | h959
                  · linarith only [h936, h958, h959, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h936, h958, h959, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h935, h958, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h939, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h964 | h964
        · linarith only [h964, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h966 | h966
          · rcases p0_3 (m.d 0 5) (by simp) with h967 | h967
            · rcases p0_3 (m.d 0 6) (by simp) with h968 | h968
              · rcases m.htr 0 1 2 (by decide) (by decide) with h969 | h969
                · linarith only [h936, h969, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h935, h936, h969, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h972 | h972
                · linarith only [h936, h972, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h935, h936, h972, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h975 | h975
              · rcases m.htr 0 1 2 (by decide) (by decide) with h976 | h976
                · linarith only [h935, h936, h976, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h935, h936, h976, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h979 | h979
                · linarith only [h936, h979, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h935, h936, h979, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h966, hlam, p0_0]
    · linarith only [h935, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h985 | h985
    · rcases p0_3 (m.d 0 2) (by simp) with h986 | h986
      · rcases p0_3 (m.d 0 3) (by simp) with h987 | h987
        · rcases p0_3 (m.d 0 4) (by simp) with h988 | h988
          · rcases p0_3 (m.d 0 5) (by simp) with h989 | h989
            · linarith only [h989, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h991 | h991
              · rcases m.htr 0 1 2 (by decide) (by decide) with h992 | h992
                · rcases m.htr 0 1 3 (by decide) (by decide) with h993 | h993
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h995 | h995
                      · linarith only [h986, h992, h995, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h986, h992, h995, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h985, h994, hlam]
                  · linarith only [h986, h992, h993, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h985, h992, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1001 | h1001
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1002 | h1002
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1003 | h1003
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1004 | h1004
                      · linarith only [h1004, h986, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h1003, h1004, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1003, h985, hlam]
                  · linarith only [h1001, h1002, h986, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1001, h985, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · linarith only [h988, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1011 | h1011
          · rcases p0_3 (m.d 0 5) (by simp) with h1012 | h1012
            · linarith only [h1012, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1014 | h1014
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1015 | h1015
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1016 | h1016
                  · linarith only [h1015, h1016, h986, h987, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1015, h1016, h986, h987, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1015, h985, h987, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1020 | h1020
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1021 | h1021
                  · linarith only [h1021, h986, h987, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1020, h1021, h986, h987, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1020, h985, h987, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1011, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1026 | h1026
        · rcases p0_3 (m.d 0 4) (by simp) with h1027 | h1027
          · rcases p0_3 (m.d 0 5) (by simp) with h1028 | h1028
            · linarith only [h1028, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1030 | h1030
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1031 | h1031
                · linarith only [h1026, h1031, h986, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1031, h985, h986, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1034 | h1034
                · linarith only [h1034, h985, h986, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1034, h985, h986, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1027, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1038 | h1038
          · rcases p0_3 (m.d 0 5) (by simp) with h1039 | h1039
            · linarith only [h1039, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1041 | h1041
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1042 | h1042
                · linarith only [h1042, h986, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1042, h985, h986, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1045 | h1045
                · linarith only [h1045, h985, h986, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1045, h985, h986, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1038, hlam, p0_0]
    · linarith only [h985, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1050 | h1050
    · rcases p0_3 (m.d 0 2) (by simp) with h1051 | h1051
      · rcases p0_3 (m.d 0 3) (by simp) with h1052 | h1052
        · rcases p0_3 (m.d 0 4) (by simp) with h1053 | h1053
          · rcases p0_3 (m.d 0 5) (by simp) with h1054 | h1054
            · rcases p0_3 (m.d 0 6) (by simp) with h1055 | h1055
              · linarith only [h1055, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1057 | h1057
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1058 | h1058
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1059 | h1059
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1060 | h1060
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1061 | h1061
                        · linarith only [h1051, h1057, h1061, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                        · linarith only [h1051, h1057, h1061, hc06, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                      · linarith only [h1051, h1057, h1060, hc06, hc15, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                    · linarith only [h1050, h1059, hlam]
                  · linarith only [h1051, h1057, h1058, hc06, hc13, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                · linarith only [h1050, h1057, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1068 | h1068
              · linarith only [h1068, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1070 | h1070
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1071 | h1071
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1072 | h1072
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1073 | h1073
                      · linarith only [h1051, h1054, h1073, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h1054, h1072, h1073, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1050, h1072, hlam]
                  · linarith only [h1051, h1054, h1070, h1071, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1050, h1054, h1070, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
          · linarith only [h1053, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1080 | h1080
          · rcases p0_3 (m.d 0 5) (by simp) with h1081 | h1081
            · rcases p0_3 (m.d 0 6) (by simp) with h1082 | h1082
              · linarith only [h1082, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1084 | h1084
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1085 | h1085
                  · linarith only [h1051, h1052, h1085, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1051, h1052, h1084, h1085, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1050, h1052, h1084, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1089 | h1089
              · linarith only [h1089, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1091 | h1091
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1092 | h1092
                  · linarith only [h1051, h1052, h1091, h1092, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1051, h1052, h1091, h1092, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1050, h1052, h1091, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1080, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1097 | h1097
        · rcases p0_3 (m.d 0 4) (by simp) with h1098 | h1098
          · rcases p0_3 (m.d 0 5) (by simp) with h1099 | h1099
            · rcases p0_3 (m.d 0 6) (by simp) with h1100 | h1100
              · linarith only [h1100, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1102 | h1102
                · linarith only [h1050, h1051, h1102, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1050, h1051, h1102, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1105 | h1105
              · linarith only [h1105, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1107 | h1107
                · linarith only [h1050, h1051, h1107, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1050, h1051, h1107, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1098, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1111 | h1111
          · rcases p0_3 (m.d 0 5) (by simp) with h1112 | h1112
            · rcases p0_3 (m.d 0 6) (by simp) with h1113 | h1113
              · linarith only [h1113, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1115 | h1115
                · linarith only [h1050, h1051, h1115, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1050, h1051, h1115, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · rcases p0_3 (m.d 0 6) (by simp) with h1118 | h1118
              · linarith only [h1118, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1120 | h1120
                · linarith only [h1050, h1051, h1120, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1050, h1051, h1120, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
          · linarith only [h1111, hlam, p0_0]
    · linarith only [h1050, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1126 | h1126
    · rcases p0_3 (m.d 0 2) (by simp) with h1127 | h1127
      · linarith only [h1127, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1129 | h1129
        · rcases p0_3 (m.d 0 4) (by simp) with h1130 | h1130
          · rcases p0_3 (m.d 0 5) (by simp) with h1131 | h1131
            · rcases p0_3 (m.d 0 6) (by simp) with h1132 | h1132
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1133 | h1133
                · linarith only [h1133, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1133, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1136 | h1136
                · linarith only [h1129, h1136, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1136, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1131, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1140 | h1140
            · rcases p0_3 (m.d 0 6) (by simp) with h1141 | h1141
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1142 | h1142
                · linarith only [h1142, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1142, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1145 | h1145
                · linarith only [h1126, h1145, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1145, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1140, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1149 | h1149
          · rcases p0_3 (m.d 0 5) (by simp) with h1150 | h1150
            · rcases p0_3 (m.d 0 6) (by simp) with h1151 | h1151
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1152 | h1152
                · linarith only [h1126, h1152, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1152, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1155 | h1155
                · linarith only [h1126, h1155, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1155, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1150, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1159 | h1159
            · rcases p0_3 (m.d 0 6) (by simp) with h1160 | h1160
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1161 | h1161
                · linarith only [h1161, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1161, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1164 | h1164
                · linarith only [h1126, h1164, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1126, h1164, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1159, hlam, p0_0]
    · linarith only [h1126, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1169 | h1169
    · rcases p0_3 (m.d 0 2) (by simp) with h1170 | h1170
      · rcases p0_3 (m.d 0 3) (by simp) with h1171 | h1171
        · linarith only [h1171, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1173 | h1173
          · rcases p0_3 (m.d 0 5) (by simp) with h1174 | h1174
            · rcases p0_3 (m.d 0 6) (by simp) with h1175 | h1175
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1176 | h1176
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1177 | h1177
                  · linarith only [h1170, h1176, h1177, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1170, h1176, h1177, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1169, h1176, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1181 | h1181
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1182 | h1182
                  · linarith only [h1170, h1182, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1170, h1181, h1182, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1169, h1181, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1174, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1187 | h1187
            · rcases p0_3 (m.d 0 6) (by simp) with h1188 | h1188
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1189 | h1189
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1190 | h1190
                  · linarith only [h1170, h1189, h1190, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1170, h1189, h1190, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1169, h1189, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1194 | h1194
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1195 | h1195
                  · linarith only [h1170, h1195, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1170, h1194, h1195, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1169, h1194, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1187, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1200 | h1200
        · linarith only [h1200, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1202 | h1202
          · rcases p0_3 (m.d 0 5) (by simp) with h1203 | h1203
            · rcases p0_3 (m.d 0 6) (by simp) with h1204 | h1204
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1205 | h1205
                · linarith only [h1169, h1170, h1205, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1169, h1170, h1205, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1208 | h1208
                · linarith only [h1169, h1170, h1208, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1169, h1170, h1208, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1203, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1212 | h1212
            · rcases p0_3 (m.d 0 6) (by simp) with h1213 | h1213
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1214 | h1214
                · linarith only [h1169, h1170, h1214, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1169, h1170, h1214, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1217 | h1217
                · linarith only [h1170, h1217, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1169, h1170, h1217, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1212, hlam, p0_0]
    · linarith only [h1169, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1222 | h1222
    · rcases p0_3 (m.d 0 2) (by simp) with h1223 | h1223
      · rcases p0_3 (m.d 0 3) (by simp) with h1224 | h1224
        · rcases p0_3 (m.d 0 4) (by simp) with h1225 | h1225
          · linarith only [h1225, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1227 | h1227
            · rcases p0_3 (m.d 0 6) (by simp) with h1228 | h1228
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1229 | h1229
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1231 | h1231
                    · linarith only [h1223, h1229, h1231, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h1223, h1229, h1231, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1223, h1229, h1230, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1222, h1229, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1238 | h1238
                    · linarith only [h1223, h1238, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h1223, h1236, h1238, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1223, h1236, h1237, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1222, h1236, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · linarith only [h1227, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1244 | h1244
          · linarith only [h1244, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1246 | h1246
            · rcases p0_3 (m.d 0 6) (by simp) with h1247 | h1247
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1248 | h1248
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1249 | h1249
                  · linarith only [h1223, h1224, h1248, h1249, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1223, h1224, h1248, h1249, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1222, h1224, h1248, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1253 | h1253
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1254 | h1254
                  · linarith only [h1223, h1224, h1253, h1254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1223, h1224, h1253, h1254, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1222, h1224, h1253, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1246, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1259 | h1259
        · rcases p0_3 (m.d 0 4) (by simp) with h1260 | h1260
          · linarith only [h1260, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1262 | h1262
            · rcases p0_3 (m.d 0 6) (by simp) with h1263 | h1263
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1264 | h1264
                · linarith only [h1222, h1223, h1264, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1222, h1223, h1264, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1267 | h1267
                · linarith only [h1222, h1223, h1267, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1222, h1223, h1267, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1262, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1271 | h1271
          · linarith only [h1271, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1273 | h1273
            · rcases p0_3 (m.d 0 6) (by simp) with h1274 | h1274
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1275 | h1275
                · linarith only [h1222, h1223, h1275, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1222, h1223, h1275, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1278 | h1278
                · linarith only [h1223, h1278, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1222, h1223, h1278, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1273, hlam, p0_0]
    · linarith only [h1222, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1284 | h1284
    · rcases p0_3 (m.d 0 2) (by simp) with h1285 | h1285
      · rcases p0_3 (m.d 0 3) (by simp) with h1286 | h1286
        · rcases p0_3 (m.d 0 4) (by simp) with h1287 | h1287
          · rcases p0_3 (m.d 0 5) (by simp) with h1288 | h1288
            · rcases p0_3 (m.d 0 6) (by simp) with h1289 | h1289
              · linarith only [h1289, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1291 | h1291
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1292 | h1292
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1293 | h1293
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1294 | h1294
                      · rcases m.htr 0 1 6 (by decide) (by decide) with h1295 | h1295
                        · linarith only [h1285, h1291, h1295, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                        · linarith only [h1285, h1291, h1295, hc06, hc16, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                      · linarith only [h1284, h1294, hlam]
                    · linarith only [h1285, h1291, h1293, hc06, hc14, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                  · linarith only [h1285, h1291, h1292, hc06, hc13, hlam, hphi, ht01, ht0b, ht6b, p0_1]
                · linarith only [h1284, h1291, hc06, hc12, hlam, hphi, ht01, ht0b, ht6b, p0_1]
            · linarith only [h1288, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1303 | h1303
            · rcases p0_3 (m.d 0 6) (by simp) with h1304 | h1304
              · linarith only [h1304, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1306 | h1306
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1307 | h1307
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1308 | h1308
                    · linarith only [h1285, h1287, h1306, h1308, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h1285, h1287, h1306, h1308, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1285, h1287, h1306, h1307, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1284, h1287, h1306, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
            · linarith only [h1303, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1314 | h1314
          · rcases p0_3 (m.d 0 5) (by simp) with h1315 | h1315
            · rcases p0_3 (m.d 0 6) (by simp) with h1316 | h1316
              · linarith only [h1316, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1318 | h1318
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1319 | h1319
                  · linarith only [h1285, h1286, h1319, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1285, h1286, h1318, h1319, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1284, h1286, h1318, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1315, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1324 | h1324
            · rcases p0_3 (m.d 0 6) (by simp) with h1325 | h1325
              · linarith only [h1325, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1327 | h1327
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1328 | h1328
                  · linarith only [h1285, h1286, h1327, h1328, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1285, h1286, h1327, h1328, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1284, h1286, h1327, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1324, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1333 | h1333
        · rcases p0_3 (m.d 0 4) (by simp) with h1334 | h1334
          · rcases p0_3 (m.d 0 5) (by simp) with h1335 | h1335
            · rcases p0_3 (m.d 0 6) (by simp) with h1336 | h1336
              · linarith only [h1336, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1338 | h1338
                · linarith only [h1284, h1285, h1338, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1284, h1285, h1338, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1335, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1342 | h1342
            · rcases p0_3 (m.d 0 6) (by simp) with h1343 | h1343
              · linarith only [h1343, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1345 | h1345
                · linarith only [h1284, h1285, h1345, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1284, h1285, h1345, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1342, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1349 | h1349
          · rcases p0_3 (m.d 0 5) (by simp) with h1350 | h1350
            · rcases p0_3 (m.d 0 6) (by simp) with h1351 | h1351
              · linarith only [h1351, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1353 | h1353
                · linarith only [h1285, h1349, h1353, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1284, h1285, h1353, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1350, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1357 | h1357
            · rcases p0_3 (m.d 0 6) (by simp) with h1358 | h1358
              · linarith only [h1358, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1360 | h1360
                · linarith only [h1285, h1360, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1284, h1285, h1360, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
            · linarith only [h1357, hlam, p0_0]
    · linarith only [h1284, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1366 | h1366
    · rcases p0_3 (m.d 0 2) (by simp) with h1367 | h1367
      · linarith only [h1367, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1369 | h1369
        · rcases p0_3 (m.d 0 4) (by simp) with h1370 | h1370
          · rcases p0_3 (m.d 0 5) (by simp) with h1371 | h1371
            · rcases p0_3 (m.d 0 6) (by simp) with h1372 | h1372
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1373 | h1373
                · linarith only [h1373, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1373, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1372, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1377 | h1377
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1378 | h1378
                · linarith only [h1366, h1378, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1378, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1377, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1382 | h1382
            · rcases p0_3 (m.d 0 6) (by simp) with h1383 | h1383
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1384 | h1384
                · linarith only [h1369, h1384, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1384, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1383, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1388 | h1388
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1389 | h1389
                · linarith only [h1366, h1389, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1389, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1388, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1393 | h1393
          · rcases p0_3 (m.d 0 5) (by simp) with h1394 | h1394
            · rcases p0_3 (m.d 0 6) (by simp) with h1395 | h1395
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1396 | h1396
                · linarith only [h1366, h1396, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1396, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1395, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1400 | h1400
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1401 | h1401
                · linarith only [h1366, h1401, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1401, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1400, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1405 | h1405
            · rcases p0_3 (m.d 0 6) (by simp) with h1406 | h1406
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1407 | h1407
                · linarith only [h1366, h1407, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1407, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1406, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1411 | h1411
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1412 | h1412
                · linarith only [h1366, h1412, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1366, h1412, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1411, hlam, p0_0]
    · linarith only [h1366, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1417 | h1417
    · rcases p0_3 (m.d 0 2) (by simp) with h1418 | h1418
      · rcases p0_3 (m.d 0 3) (by simp) with h1419 | h1419
        · linarith only [h1419, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1421 | h1421
          · rcases p0_3 (m.d 0 5) (by simp) with h1422 | h1422
            · rcases p0_3 (m.d 0 6) (by simp) with h1423 | h1423
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1424 | h1424
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h1418, h1424, h1425, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1418, h1424, h1425, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1417, h1424, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1423, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1430 | h1430
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1431 | h1431
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1432 | h1432
                  · linarith only [h1418, h1432, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1418, h1431, h1432, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1417, h1431, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1430, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1437 | h1437
            · rcases p0_3 (m.d 0 6) (by simp) with h1438 | h1438
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1439 | h1439
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1440 | h1440
                  · linarith only [h1418, h1439, h1440, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1418, h1439, h1440, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1417, h1439, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1438, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1445 | h1445
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1446 | h1446
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1447 | h1447
                  · linarith only [h1418, h1447, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1418, h1446, h1447, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1417, h1446, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1445, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1452 | h1452
        · linarith only [h1452, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1454 | h1454
          · rcases p0_3 (m.d 0 5) (by simp) with h1455 | h1455
            · rcases p0_3 (m.d 0 6) (by simp) with h1456 | h1456
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1457 | h1457
                · linarith only [h1417, h1418, h1457, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1417, h1418, h1457, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1456, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1461 | h1461
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1462 | h1462
                · linarith only [h1418, h1454, h1462, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1417, h1418, h1462, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1461, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1466 | h1466
            · rcases p0_3 (m.d 0 6) (by simp) with h1467 | h1467
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1468 | h1468
                · linarith only [h1417, h1418, h1468, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1417, h1418, h1468, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1467, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1472 | h1472
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1473 | h1473
                · linarith only [h1418, h1473, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1417, h1418, h1473, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1472, hlam, p0_0]
    · linarith only [h1417, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1478 | h1478
    · rcases p0_3 (m.d 0 2) (by simp) with h1479 | h1479
      · rcases p0_3 (m.d 0 3) (by simp) with h1480 | h1480
        · rcases p0_3 (m.d 0 4) (by simp) with h1481 | h1481
          · linarith only [h1481, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1483 | h1483
            · rcases p0_3 (m.d 0 6) (by simp) with h1484 | h1484
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1485 | h1485
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1486 | h1486
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1487 | h1487
                    · linarith only [h1479, h1485, h1487, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h1479, h1485, h1487, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1479, h1485, h1486, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1478, h1485, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1484, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1493 | h1493
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1494 | h1494
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1495 | h1495
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1496 | h1496
                    · linarith only [h1479, h1496, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h1479, h1494, h1496, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1479, h1494, h1495, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1478, h1494, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1493, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1502 | h1502
          · linarith only [h1502, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1504 | h1504
            · rcases p0_3 (m.d 0 6) (by simp) with h1505 | h1505
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1506 | h1506
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1507 | h1507
                  · linarith only [h1479, h1480, h1507, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1479, h1480, h1506, h1507, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1478, h1480, h1506, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1505, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1512 | h1512
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1513 | h1513
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1514 | h1514
                  · linarith only [h1479, h1480, h1513, h1514, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1479, h1480, h1513, h1514, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1478, h1480, h1513, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1512, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1519 | h1519
        · rcases p0_3 (m.d 0 4) (by simp) with h1520 | h1520
          · linarith only [h1520, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1522 | h1522
            · rcases p0_3 (m.d 0 6) (by simp) with h1523 | h1523
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1524 | h1524
                · linarith only [h1478, h1479, h1524, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1478, h1479, h1524, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1523, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1528 | h1528
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1529 | h1529
                · linarith only [h1479, h1519, h1529, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1478, h1479, h1529, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1528, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1533 | h1533
          · linarith only [h1533, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1535 | h1535
            · rcases p0_3 (m.d 0 6) (by simp) with h1536 | h1536
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1537 | h1537
                · linarith only [h1478, h1479, h1537, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1478, h1479, h1537, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1536, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1541 | h1541
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1542 | h1542
                · linarith only [h1478, h1479, h1542, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1478, h1479, h1542, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1541, hlam, p0_0]
    · linarith only [h1478, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1547 | h1547
    · rcases p0_3 (m.d 0 2) (by simp) with h1548 | h1548
      · rcases p0_3 (m.d 0 3) (by simp) with h1549 | h1549
        · rcases p0_3 (m.d 0 4) (by simp) with h1550 | h1550
          · rcases p0_3 (m.d 0 5) (by simp) with h1551 | h1551
            · linarith only [h1551, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1553 | h1553
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1554 | h1554
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1555 | h1555
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1556 | h1556
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1557 | h1557
                      · linarith only [h1548, h1554, h1557, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                      · linarith only [h1548, h1554, h1557, hc05, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                    · linarith only [h1548, h1554, h1556, hc05, hc14, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                  · linarith only [h1548, h1554, h1555, hc05, hc13, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
                · linarith only [h1547, h1554, hc05, hc12, hlam, hphi, ht01, ht0b, ht56, ht6b, p0_1]
              · linarith only [h1553, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1564 | h1564
            · linarith only [h1564, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1566 | h1566
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1567 | h1567
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1568 | h1568
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1569 | h1569
                    · linarith only [h1548, h1550, h1569, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                    · linarith only [h1548, h1550, h1567, h1569, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                  · linarith only [h1548, h1550, h1567, h1568, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
                · linarith only [h1547, h1550, h1567, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, p0_1]
              · linarith only [h1566, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1575 | h1575
          · rcases p0_3 (m.d 0 5) (by simp) with h1576 | h1576
            · linarith only [h1576, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1578 | h1578
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1579 | h1579
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1580 | h1580
                  · linarith only [h1548, h1549, h1579, h1580, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1548, h1549, h1579, h1580, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1547, h1549, h1579, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1578, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1585 | h1585
            · linarith only [h1585, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1587 | h1587
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1588 | h1588
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1589 | h1589
                  · linarith only [h1548, h1549, h1589, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                  · linarith only [h1548, h1549, h1588, h1589, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                · linarith only [h1547, h1549, h1588, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1587, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h1594 | h1594
        · rcases p0_3 (m.d 0 4) (by simp) with h1595 | h1595
          · rcases p0_3 (m.d 0 5) (by simp) with h1596 | h1596
            · linarith only [h1596, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1598 | h1598
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1599 | h1599
                · linarith only [h1548, h1594, h1599, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1547, h1548, h1599, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1598, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1603 | h1603
            · linarith only [h1603, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1605 | h1605
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1606 | h1606
                · linarith only [h1547, h1548, h1606, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1547, h1548, h1606, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1605, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h1610 | h1610
          · rcases p0_3 (m.d 0 5) (by simp) with h1611 | h1611
            · linarith only [h1611, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1613 | h1613
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1614 | h1614
                · linarith only [h1548, h1610, h1614, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1547, h1548, h1614, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1613, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h1618 | h1618
            · linarith only [h1618, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h1620 | h1620
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1621 | h1621
                · linarith only [h1548, h1621, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                · linarith only [h1547, h1548, h1621, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
              · linarith only [h1620, hlam, p0_0]
    · linarith only [h1547, hc06, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_H_I_M_LI (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
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
  have u1elo5 := h1elo (m.d 1 6) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0 | h0
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
  · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
    · rcases m.htr 0 1 3 (by decide) (by decide) with h59 | h59
      · rcases m.htr 0 1 4 (by decide) (by decide) with h60 | h60
        · rcases m.htr 0 1 5 (by decide) (by decide) with h61 | h61
          · rcases m.htr 0 1 6 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h62, hlam, ht01, u1elo0]
            · linarith only [h0, h62, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h65 | h65
            · linarith only [h0, h61, h65, hlam, ht01, u1elo4]
            · linarith only [h0, h65, hlam, ht01, u1elo5]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 0 1 6 (by decide) (by decide) with h69 | h69
            · linarith only [h0, h60, h69, hlam, ht01, u1elo3]
            · linarith only [h0, h69, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h72 | h72
            · linarith only [h0, h60, h72, hlam, ht01, u1elo3]
            · linarith only [h0, h72, hlam, ht01, u1elo5]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h75 | h75
        · rcases m.htr 0 1 5 (by decide) (by decide) with h76 | h76
          · rcases m.htr 0 1 6 (by decide) (by decide) with h77 | h77
            · linarith only [h0, h59, h77, hlam, ht01, u1elo2]
            · linarith only [h0, h77, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h80 | h80
            · linarith only [h0, h59, h80, hlam, ht01, u1elo2]
            · linarith only [h0, h80, hlam, ht01, u1elo5]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h83 | h83
          · rcases m.htr 0 1 6 (by decide) (by decide) with h84 | h84
            · linarith only [h0, h59, h84, hlam, ht01, u1elo2]
            · linarith only [h0, h84, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h87 | h87
            · linarith only [h0, h59, h87, hlam, ht01, u1elo2]
            · linarith only [h0, h87, hlam, ht01, u1elo5]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h90 | h90
      · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
        · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
          · rcases m.htr 0 1 6 (by decide) (by decide) with h93 | h93
            · linarith only [h0, h58, h93, hlam, ht01, u1elo1]
            · linarith only [h0, h93, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h96 | h96
            · linarith only [h0, h58, h96, hlam, ht01, u1elo1]
            · linarith only [h0, h96, hlam, ht01, u1elo5]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h99 | h99
          · rcases m.htr 0 1 6 (by decide) (by decide) with h100 | h100
            · linarith only [h0, h100, h58, hlam, ht01, u1elo1]
            · linarith only [h0, h100, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h103 | h103
            · linarith only [h0, h103, h58, hlam, ht01, u1elo1]
            · linarith only [h0, h103, hlam, ht01, u1elo5]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
        · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
          · rcases m.htr 0 1 6 (by decide) (by decide) with h108 | h108
            · linarith only [h0, h108, h58, hlam, ht01, u1elo1]
            · linarith only [h0, h108, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h111 | h111
            · linarith only [h0, h111, h58, hlam, ht01, u1elo1]
            · linarith only [h0, h111, hlam, ht01, u1elo5]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h114 | h114
          · rcases m.htr 0 1 6 (by decide) (by decide) with h115 | h115
            · linarith only [h0, h115, h58, hlam, ht01, u1elo1]
            · linarith only [h0, h115, hlam, ht01, u1elo5]
          · rcases m.htr 0 1 6 (by decide) (by decide) with h118 | h118
            · linarith only [h0, h118, h58, hlam, ht01, u1elo1]
            · linarith only [h0, h118, hlam, ht01, u1elo5]

theorem n8l_sAA8_H_I_M_LR (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi6 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo2]

theorem n8l_sAA8_H_L_H_I (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h9, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h15 | h15
    · linarith only [h15, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h15, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h39, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h50 | h50
    · linarith only [h50, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h50, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h53 | h53
    · linarith only [h53, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h53, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h56 | h56
    · linarith only [h56, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h56, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h60 | h60
    · linarith only [h60, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h60, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h64 | h64
    · linarith only [h64, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h64, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · linarith only [h67, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h67, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · linarith only [h70, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h70, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h73 | h73
    · linarith only [h73, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h73, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_H_L_H_L (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
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
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h2, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h2, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                · rcases m.htr 1 5 6 (by decide) (by decide) with h12 | h12
                  · linarith only [h12, h3, hc56, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h10, h14, h17, h4, h6, hc12, hc23, hlam, hphi]
                          · linarith only [h16, h17, h4, h6, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h14, h16, h20, hlam]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h22 | h22
                            · linarith only [h10, h12, h15, h22, h4, h6, hc12, hc23, hlam, hphi]
                            · rcases m.htr 4 5 6 (by decide) (by decide) with h24 | h24
                              · linarith only [h22, h24, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h14, h16, h24, h4, h6, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                      · linarith only [h14, h15, h4, h6, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h14, h28, h4, h8, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h32 | h32
                            · rcases m.htr 4 5 6 (by decide) (by decide) with h33 | h33
                              · linarith only [h10, h12, h30, h33, h4, h6, hc12, hc24, hlam, hphi]
                              · linarith only [h10, h31, h32, h33, h4, h6, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h28, h32, h4, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                          · linarith only [h14, h31, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h14, h30, h38, h4, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h14, h38, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n8l_sAA8_H_L_H_R (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo0, u1ehi0]

theorem n8l_sAA8_H_L_M_IR (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 1 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo0, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo0, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1, u1ehi4]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1, u1ehi5]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h8 | h8
          · rcases m.htr 0 3 6 (by decide) (by decide) with h9 | h9
            · rcases m.htr 0 5 6 (by decide) (by decide) with h10 | h10
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                · rcases m.htr 1 2 6 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 1 3 6 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 1 5 6 (by decide) (by decide) with h14 | h14
                      · rcases m.htr 2 3 6 (by decide) (by decide) with h15 | h15
                        · linarith only [h15, h8, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                        · linarith only [h15, h8, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                      · linarith only [h10, h14, hc15, hlam, hphi, ht0b, ht56, ht6b, u0elo4]
                    · linarith only [h13, h8, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                  · linarith only [h0, h12, hc26, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h11, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                · rcases m.htr 1 2 6 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 1 3 6 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 1 5 6 (by decide) (by decide) with h25 | h25
                      · linarith only [h10, h25, h4, hc15, hlam, hphi, u1ehi0]
                      · linarith only [h25, h4, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0]
                    · linarith only [h24, h8, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                  · linarith only [h2, h22, h23, hc26, hlam, hphi, ht12, u1ehi0]
                · linarith only [h22, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 2 6 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 1 3 6 (by decide) (by decide) with h34 | h34
                    · linarith only [h2, h32, h34, h9, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h2, h34, hc36, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h33, hc26, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h32, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                · rcases m.htr 1 2 6 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 1 3 6 (by decide) (by decide) with h41 | h41
                    · linarith only [h2, h39, h41, h9, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h2, h41, hc36, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h40, hc26, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h39, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1, u1ehi0]
          · rcases m.htr 0 3 6 (by decide) (by decide) with h46 | h46
            · rcases m.htr 0 5 6 (by decide) (by decide) with h47 | h47
              · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h48, h8, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h48, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                · linarith only [h0, h51, h8, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h51, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 5 6 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h55, h8, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h55, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                · linarith only [h0, h58, h8, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h58, hc23, hlam, hphi, ht12, u1ehi0]

theorem n8l_sAA8_H_L_M_LI (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u1elo5 := h1elo (m.d 1 6) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h9, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h12, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h15 | h15
    · linarith only [h15, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h15, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h26, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h39, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h43, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h46, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h50 | h50
    · linarith only [h50, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h50, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h53 | h53
    · linarith only [h53, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h53, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h56 | h56
    · linarith only [h56, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h56, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h60 | h60
    · linarith only [h60, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h60, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h64 | h64
    · linarith only [h64, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h64, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · linarith only [h67, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h67, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · linarith only [h70, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h70, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h73 | h73
    · linarith only [h73, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h73, hc01, hlam, hphi, p0_1, u1elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_H_L_M_LR (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi6 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo0, u1ehi8]
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo2]

theorem n8l_sAA8_H_R_H_L (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n8l_sAA8_H_R_H_R (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 6 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 5 6 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 6 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 5 6 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h1, h13, h8, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h1, h11, h13, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h1, h16, h8, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h1, h11, h16, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · rcases m.htr 2 5 6 (by decide) (by decide) with h19 | h19
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h11, h20, h8, hlam]
                            · rcases m.htr 3 5 6 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h1, h22, h9, hc01, hc56, hlam, hphi, ht0b, ht6b]
                              · linarith only [h0, h19, h2, h22, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                            · linarith only [h0, h1, h25, h8, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 3 5 6 (by decide) (by decide) with h27 | h27
                              · linarith only [h0, h1, h11, h19, h27, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                              · rcases m.htr 4 5 6 (by decide) (by decide) with h29 | h29
                                · linarith only [h0, h1, h11, h19, h29, h3, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                · linarith only [h0, h1, h11, h29, h3, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · linarith only [h0, h1, h10, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                    · linarith only [h0, h1, h4, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h1, h3, h34, h8, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                    · rcases m.htr 2 3 6 (by decide) (by decide) with h36 | h36
                      · linarith only [h0, h1, h3, h36, h8, hc01, hc36, hlam, hphi, ht0b, ht6b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 2 5 6 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 3 5 6 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 4 5 6 (by decide) (by decide) with h42 | h42
                                · linarith only [h0, h1, h3, h38, h42, h8, hc01, hc56, hlam, hphi, ht0b, ht6b]
                                · linarith only [h0, h2, h39, h42, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                              · linarith only [h34, h39, h41, hlam]
                            · linarith only [h0, h1, h3, h40, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                            · rcases m.htr 3 5 6 (by decide) (by decide) with h48 | h48
                              · linarith only [h0, h1, h3, h39, h47, h48, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                              · linarith only [h0, h1, h3, h34, h48, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h0, h2, h38, h47, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 2 5 6 (by decide) (by decide) with h52 | h52
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h0, h1, h3, h38, h52, h53, hc01, hc56, hlam, hphi, ht0b, ht6b]
                            · linarith only [h0, h1, h3, h53, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                            · linarith only [h0, h1, h3, h38, h56, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                            · linarith only [h0, h1, h3, h56, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h7, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
            · linarith only [h5, hc36, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h3, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h3, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc25, hlam, hphi, ht12, u1ehi1]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

set_option maxHeartbeats 3578000 in
theorem n8l_sAA8_H_R_M_IR (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 1 6) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases p0_3 (m.d 1 6) (by simp) with h11 | h11
              · linarith only [h11, hc16, hlam, hphi, p0_1, u1ehi1]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
                · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h15 | h15
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h17 | h17
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
                              · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h24 | h24
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h27 | h27
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h29 | h29
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h30 | h30
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                                                    · linarith only [h21, h31, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h21, h25, h31, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                                                    · linarith only [h21, h34, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h21, h25, h34, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h37 | h37
                                                  · linarith only [h28, h29, h37, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                                                    · linarith only [h21, h39, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h21, h25, h39, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h42 | h42
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h43 | h43
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                                                    · linarith only [h21, h44, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h21, h25, h44, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h28, h42, h43, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h48 | h48
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                                                    · linarith only [h21, h49, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h21, h25, h49, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                                                    · linarith only [h21, h52, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h21, h25, h52, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h56 | h56
                                                · linarith only [h25, h27, h56, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h58 | h58
                                                  · linarith only [h26, h27, h58, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                                                    · linarith only [h21, h60, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h24, h25, h27, h60, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h63 | h63
                                                · linarith only [h26, h27, h55, h63, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h65 | h65
                                                  · linarith only [h26, h27, h65, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                                                    · linarith only [h21, h67, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h24, h25, h27, h67, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h70 | h70
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
                                              · linarith only [h25, h26, h71, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h73 | h73
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h74 | h74
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                                                    · linarith only [h21, h75, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h25, h26, h75, hc23, hc35, hlam, hphi]
                                                  · linarith only [h25, h26, h73, h74, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h79 | h79
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                                                    · linarith only [h21, h80, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h23, h25, h26, h80, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h26, h70, h79, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                                              · linarith only [h25, h26, h84, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h86 | h86
                                                · linarith only [h25, h70, h86, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h88 | h88
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                                                    · linarith only [h21, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h23, h25, h70, h88, h89, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                                                    · linarith only [h21, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h25, h26, h92, hc23, hc35, hlam, hphi]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h96 | h96
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h98 | h98
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h99 | h99
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                                                    · linarith only [h100, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                                                      · linarith only [h100, h102, h22, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · linarith only [h102, h13, h17, h18, h25, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                                                    · linarith only [h105, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                                                      · linarith only [h105, h107, h22, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · linarith only [h107, h13, h17, h18, h25, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                · linarith only [h25, h96, h98, hlam]
                                              · linarith only [h25, h95, h97, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h113 | h113
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h114 | h114
                                                  · linarith only [h114, h95, h96, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                                                    · linarith only [h116, h21, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                                                      · linarith only [h116, h118, h22, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · linarith only [h113, h118, h22, h95, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h121 | h121
                                                  · linarith only [h113, h121, h25, h95, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                                                    · linarith only [h123, h21, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                                                      · linarith only [h123, h125, h22, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · linarith only [h113, h125, h24, h25, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · linarith only [h112, h25, h95, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h129 | h129
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h131 | h131
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h132 | h132
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                                                    · linarith only [h133, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                                                      · linarith only [h129, h133, h135, h22, h95, hc12, hlam, hphi, u1ehi5]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h137 | h137
                                                        · linarith only [h133, h137, h22, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                                        · linarith only [h129, h137, h25, hc23, hc34, hlam, hphi]
                                                  · linarith only [h129, h132, h95, hlam]
                                                · linarith only [h129, h130, h131, h95, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h142 | h142
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h143 | h143
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                                                    · linarith only [h129, h144, h25, hc23, hlam, hphi, ht12, u1ehi5]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                                                      · linarith only [h129, h144, h146, h22, h95, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h148 | h148
                                                        · linarith only [h144, h148, h22, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                                        · linarith only [h129, h148, h25, hc23, hc34, hlam, hphi]
                                                  · linarith only [h129, h130, h143, h25, hlam]
                                                · linarith only [h129, h142, h25, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h154 | h154
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h155 | h155
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                                                    · linarith only [h156, h21, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                                      · linarith only [h156, h158, h22, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h160 | h160
                                                        · linarith only [h129, h156, h160, h22, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h162 | h162
                                                          · linarith only [h162, h22, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h154, h156, h162, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                                                    · linarith only [h165, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                                                      · linarith only [h165, h167, h22, h95, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h169 | h169
                                                        · linarith only [h129, h165, h169, h22, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h171 | h171
                                                          · linarith only [h171, h22, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h154, h165, h171, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h174 | h174
                                                  · linarith only [h153, h154, h174, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                                                    · linarith only [h176, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                                      · linarith only [h176, h178, h22, h95, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h180 | h180
                                                        · linarith only [h129, h176, h180, h22, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h182 | h182
                                                          · linarith only [h154, h182, h22, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h184 | h184
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h185 | h185
                                                              · linarith only [h153, h154, h185, h95, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                              · linarith only [h185, h25, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                            · linarith only [h184, h25, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h189 | h189
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h190 | h190
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                                                    · linarith only [h191, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                                                      · linarith only [h191, h193, h22, h95, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h195 | h195
                                                        · linarith only [h129, h191, h195, h22, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h197 | h197
                                                          · linarith only [h197, h22, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h189, h191, h197, h22, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h153, h189, h190, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h201 | h201
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                                                    · linarith only [h202, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                                                      · linarith only [h202, h204, h22, h95, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h206 | h206
                                                        · linarith only [h129, h202, h206, h22, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h208 | h208
                                                          · linarith only [h189, h208, h22, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                                                            · linarith only [h153, h210, h25, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h13, h17, h18, h20, h210, h25, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                                                    · linarith only [h213, h25, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                                                      · linarith only [h213, h215, h22, h95, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h217 | h217
                                                        · linarith only [h129, h213, h217, h22, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h219 | h219
                                                          · linarith only [h189, h219, h22, h25, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                                                            · linarith only [h153, h221, h25, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h13, h17, h18, h20, h221, h25, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                      · linarith only [h11, h24, hlam]
                                    · linarith only [h23, h9, hlam]
                                  · linarith only [h22, h7, hlam]
                                · linarith only [h21, h5, hlam]
                              · linarith only [h20, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h19, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h18, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h17, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h16, h9, hlam, p0_1]
                    · linarith only [h15, h7, hlam, p0_1]
                  · linarith only [h14, hc13, hlam, hphi, p0_1, u1ehi1]
                · linarith only [h13, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h237 | h237
    · rcases p0_3 (m.d 1 2) (by simp) with h238 | h238
      · linarith only [h238, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h240 | h240
        · linarith only [h240, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
          · linarith only [h242, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h244 | h244
            · linarith only [h244, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases p0_3 (m.d 1 6) (by simp) with h246 | h246
              · linarith only [h246, hc16, hlam, hphi, p0_1, u1ehi2]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h248 | h248
                · rcases m.htr 0 1 3 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h251 | h251
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h252 | h252
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h254 | h254
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
                              · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
                                · linarith only [h238, h256, hlam]
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h260 | h260
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h263 | h263
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h264 | h264
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h265 | h265
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h266 | h266
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h269 | h269
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h270 | h270
                                                          · linarith only [h256, h258, h270, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h256, h258, h265, h270, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h256, h258, h264, h266, h269, hc36, hlam, hphi, ht12, ht23, u1ehi5]
                                                      · linarith only [h256, h258, h264, h266, h268, hc35, hlam, hphi, ht12, ht23, u1ehi5]
                                                    · linarith only [h256, h258, h264, h266, h267, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h278 | h278
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h279 | h279
                                                          · linarith only [h256, h258, h279, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h256, h258, h265, h279, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h256, h278, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h256, h277, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                                    · linarith only [h256, h276, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h285 | h285
                                                  · linarith only [h264, h265, h285, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h288 | h288
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h289 | h289
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h290 | h290
                                                          · linarith only [h256, h258, h264, h265, h290, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
                                                            · linarith only [h256, h260, h287, h290, h292, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h264, h265, h292, hc34, hc46, hlam, hphi]
                                                        · linarith only [h256, h289, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h256, h288, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                                    · linarith only [h256, h287, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h298 | h298
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h299 | h299
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h302 | h302
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h303 | h303
                                                          · linarith only [h256, h258, h303, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h248, h252, h253, h255, h264, h298, h303, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                        · linarith only [h256, h302, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h256, h259, h264, h298, h301, hc35, hlam, hphi, ht12, ht23, u1ehi5]
                                                    · linarith only [h256, h259, h264, h298, h300, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h264, h298, h299, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h310 | h310
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h313 | h313
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h314 | h314
                                                          · linarith only [h256, h258, h298, h314, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
                                                            · linarith only [h256, h260, h311, h314, h316, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h318 | h318
                                                              · linarith only [h256, h260, h298, h311, h314, h318, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h320 | h320
                                                                · linarith only [h256, h259, h312, h320, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                                · linarith only [h256, h259, h310, h320, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                        · linarith only [h256, h313, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h256, h312, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                                    · linarith only [h256, h259, h298, h310, h311, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h328 | h328
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h329 | h329
                                                          · linarith only [h256, h258, h298, h329, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h331 | h331
                                                            · linarith only [h256, h260, h264, h326, h329, h331, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h333 | h333
                                                              · linarith only [h256, h260, h298, h326, h329, h333, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h335 | h335
                                                                · linarith only [h256, h259, h310, h327, h335, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h337 | h337
                                                                  · linarith only [h264, h310, h337, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                                                                  · linarith only [h264, h337, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3]
                                                        · linarith only [h256, h328, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h248, h252, h254, h256, h259, h327, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                                                    · linarith only [h256, h260, h264, h310, h326, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                            · linarith only [h246, h263, hlam]
                                          · linarith only [h244, h262, hlam]
                                        · linarith only [h242, h261, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h348 | h348
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h350 | h350
                                                · linarith only [h258, h260, h350, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h352 | h352
                                                  · linarith only [h259, h260, h352, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h356 | h356
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h357 | h357
                                                          · linarith only [h258, h349, h350, h357, hc12, hlam, hphi, u1ehi4]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                                                            · linarith only [h248, h252, h258, h260, h354, h356, h359, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                            · linarith only [h346, h349, h359, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h256, h258, h356, hc36, hlam, hphi, ht12, ht23, u1ehi3]
                                                      · linarith only [h256, h258, h349, h355, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                    · linarith only [h256, h258, h349, h354, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h365 | h365
                                                · linarith only [h259, h260, h349, h365, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h367 | h367
                                                  · linarith only [h259, h260, h367, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h369 | h369
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h370 | h370
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h371 | h371
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h372 | h372
                                                          · linarith only [h258, h260, h348, h365, h372, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h374 | h374
                                                            · linarith only [h258, h260, h348, h349, h369, h374, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h376 | h376
                                                              · linarith only [h259, h260, h370, h372, h374, h376, hlam]
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h378 | h378
                                                                · linarith only [h259, h260, h348, h367, h370, h378, hc01, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h380 | h380
                                                                  · linarith only [h349, h367, h380, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                                                                  · linarith only [h349, h380, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3]
                                                        · linarith only [h348, h371, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h256, h370, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                                    · linarith only [h256, h259, h349, h369, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                            · linarith only [h246, h348, hlam]
                                          · linarith only [h244, h347, hlam]
                                        · linarith only [h242, h346, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h389 | h389
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h392 | h392
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                                              · linarith only [h258, h259, h393, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h395 | h395
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h396 | h396
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h399 | h399
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h400 | h400
                                                          · linarith only [h256, h258, h400, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · linarith only [h258, h259, h391, h395, h400, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h258, h259, h395, h398, h399, hc36, hlam, hphi, ht12, ht23, u1ehi5]
                                                      · linarith only [h391, h398, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h256, h258, h395, h397, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h258, h259, h395, h396, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h407 | h407
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h410 | h410
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h411 | h411
                                                          · linarith only [h258, h259, h391, h395, h411, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                                                            · linarith only [h259, h389, h391, h393, h408, h411, h413, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h415 | h415
                                                              · linarith only [h259, h389, h391, h395, h408, h411, h415, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h417 | h417
                                                                · linarith only [h391, h417, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                                · linarith only [h391, h407, h417, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                        · linarith only [h259, h409, h410, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h248, h252, h254, h256, h389, h409, hc01, hc26, hlam, hphi, ht0b, ht6b]
                                                    · linarith only [h256, h408, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · linarith only [h259, h389, h407, hlam]
                                            · linarith only [h246, h392, hlam]
                                          · linarith only [h244, h391, hlam]
                                        · linarith only [h242, h390, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h429 | h429
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h430 | h430
                                              · linarith only [h258, h259, h430, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h432 | h432
                                                · linarith only [h258, h389, h432, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h434 | h434
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h437 | h437
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h438 | h438
                                                          · linarith only [h258, h259, h432, h436, h438, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h440 | h440
                                                            · linarith only [h258, h389, h428, h430, h434, h435, h440, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h442 | h442
                                                              · linarith only [h258, h389, h435, h438, h442, hlam]
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h444 | h444
                                                                · linarith only [h428, h444, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                                · linarith only [h428, h434, h444, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                        · linarith only [h256, h437, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h256, h258, h436, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                                    · linarith only [h256, h258, h435, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h452 | h452
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h453 | h453
                                                          · linarith only [h256, h258, h453, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                                                            · linarith only [h258, h259, h429, h430, h434, h450, h455, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi3]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h457 | h457
                                                              · linarith only [h258, h389, h450, h453, h457, hlam]
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h459 | h459
                                                                · linarith only [h259, h428, h434, h459, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h461 | h461
                                                                  · linarith only [h258, h259, h434, h461, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                                                                  · linarith only [h430, h461, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3]
                                                        · linarith only [h429, h452, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h256, h258, h451, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                                    · linarith only [h256, h258, h450, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                            · linarith only [h246, h429, hlam]
                                          · linarith only [h244, h428, hlam]
                                        · linarith only [h242, h427, hlam]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h471 | h471
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h474 | h474
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h476 | h476
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h477 | h477
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h478 | h478
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h479 | h479
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h480 | h480
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h481 | h481
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h482 | h482
                                                            · linarith only [h472, h482, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h472, h475, h482, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h258, h470, h477, h481, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi5]
                                                        · linarith only [h258, h470, h477, h478, h480, hc36, hlam, hphi, ht12, ht23, u1ehi5]
                                                      · linarith only [h258, h470, h477, h478, h479, hc35, hlam, hphi, ht12, ht23, u1ehi5]
                                                    · linarith only [h248, h252, h253, h256, h470, h477, h478, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h489 | h489
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h490 | h490
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h491 | h491
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h492 | h492
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h493 | h493
                                                            · linarith only [h472, h493, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h472, h475, h493, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h258, h492, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                                        · linarith only [h258, h471, h477, h489, h491, hc36, hlam, hphi, ht12, ht23, u1ehi4]
                                                      · linarith only [h258, h471, h477, h489, h490, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                    · linarith only [h248, h252, h253, h256, h471, h477, h489, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi4]
                                                · linarith only [h258, h471, h476, hlam]
                                              · linarith only [h258, h470, h475, hlam]
                                            · linarith only [h246, h474, hlam]
                                          · linarith only [h244, h473, hlam]
                                        · linarith only [h242, h472, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h507 | h507
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h509 | h509
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h510 | h510
                                                  · linarith only [h470, h471, h510, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h513 | h513
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h514 | h514
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h515 | h515
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                                                            · linarith only [h505, h516, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h505, h508, h516, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h505, h509, h515, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h258, h512, h514, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h258, h470, h512, h513, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                    · linarith only [h256, h470, h512, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h523 | h523
                                                  · linarith only [h258, h470, h509, h523, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h525 | h525
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h526 | h526
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h527 | h527
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h528 | h528
                                                          · linarith only [h258, h509, h525, h528, hc23, hlam, hphi, ht12, u1ehi1]
                                                          · linarith only [h258, h470, h528, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                                                        · linarith only [h507, h527, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h258, h470, h525, h526, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                    · linarith only [h256, h470, h505, h525, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi4]
                                              · linarith only [h258, h470, h508, hlam]
                                            · linarith only [h246, h507, hlam]
                                          · linarith only [h244, h506, hlam]
                                        · linarith only [h242, h505, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h538 | h538
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h541 | h541
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h543 | h543
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h544 | h544
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h546 | h546
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h547 | h547
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h548 | h548
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                                                            · linarith only [h539, h549, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h539, h542, h549, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h258, h548, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                                        · linarith only [h258, h538, h545, h547, hc36, hlam, hphi, ht12, ht23, u1ehi5]
                                                      · linarith only [h258, h538, h545, h546, hc35, hlam, hphi, ht12, ht23, u1ehi5]
                                                    · linarith only [h256, h538, h545, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h470, h538, h544, hlam]
                                                · linarith only [h258, h538, h543, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h558 | h558
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h559 | h559
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h561 | h561
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h562 | h562
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h563 | h563
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                                                            · linarith only [h258, h538, h539, h542, h564, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h566 | h566
                                                              · linarith only [h540, h564, h566, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                              · linarith only [h542, h558, h566, hc34, hc45, hlam, hphi]
                                                          · linarith only [h248, h252, h253, h255, h258, h538, h542, h558, h563, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                                                        · linarith only [h258, h538, h560, h562, hc36, hlam, hphi, ht12, ht23, u1ehi5]
                                                      · linarith only [h258, h538, h540, h560, h561, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                                                    · linarith only [h256, h538, h560, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h470, h538, h559, hlam]
                                                · linarith only [h258, h538, h558, hlam]
                                            · linarith only [h246, h541, hlam]
                                          · linarith only [h244, h540, hlam]
                                        · linarith only [h242, h539, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h580 | h580
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h581 | h581
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h582 | h582
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h583 | h583
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h586 | h586
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h587 | h587
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h588 | h588
                                                            · linarith only [h578, h588, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h578, h581, h588, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h578, h582, h587, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h258, h584, h586, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h258, h584, h585, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                                    · linarith only [h256, h584, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h596 | h596
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h597 | h597
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h598 | h598
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                                                            · linarith only [h578, h599, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · linarith only [h578, h581, h599, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h578, h582, h598, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                        · linarith only [h258, h580, h595, h597, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                      · linarith only [h258, h579, h595, h596, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                    · linarith only [h256, h595, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h606 | h606
                                                  · linarith only [h581, h582, h606, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h610 | h610
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h611 | h611
                                                          · linarith only [h582, h608, h611, hc23, hlam, hphi, ht12, u1ehi3]
                                                          · linarith only [h258, h611, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                                        · linarith only [h580, h610, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h258, h579, h608, h609, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                    · linarith only [h256, h578, h608, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h617 | h617
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h618 | h618
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h620 | h620
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h621 | h621
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h622 | h622
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h623 | h623
                                                            · linarith only [h578, h623, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h625 | h625
                                                              · linarith only [h579, h623, h625, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                              · linarith only [h581, h617, h625, hc34, hc45, hlam, hphi]
                                                          · linarith only [h248, h252, h253, h255, h581, h617, h622, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                        · linarith only [h258, h580, h619, h621, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                      · linarith only [h258, h579, h619, h620, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                    · linarith only [h248, h252, h253, h256, h619, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                  · linarith only [h581, h617, h618, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h633 | h633
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h635 | h635
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h636 | h636
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h637 | h637
                                                          · linarith only [h617, h634, h637, hc23, hlam, hphi, ht12, u1ehi3]
                                                          · linarith only [h258, h637, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                                        · linarith only [h580, h636, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h258, h579, h634, h635, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                    · linarith only [h256, h578, h634, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h645 | h645
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h646 | h646
                                                          · linarith only [h617, h643, h646, hc23, hlam, hphi, ht12, u1ehi3]
                                                          · linarith only [h258, h646, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                                        · linarith only [h580, h645, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · linarith only [h258, h579, h643, h644, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi1]
                                                    · linarith only [h578, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                            · linarith only [h246, h580, hlam]
                                          · linarith only [h244, h579, hlam]
                                        · linarith only [h242, h578, hlam]
                              · linarith only [h255, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h254, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h253, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h252, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h251, hc15, hlam, hphi, p0_1, u1ehi2]
                    · linarith only [h242, h250, hlam, p0_1]
                  · linarith only [h249, hlam, p0_0]
                · linarith only [h248, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h237, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h664 | h664
    · rcases p0_3 (m.d 1 2) (by simp) with h665 | h665
      · linarith only [h665, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h667 | h667
        · linarith only [h667, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h669 | h669
          · linarith only [h669, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h671 | h671
            · linarith only [h671, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases p0_3 (m.d 1 6) (by simp) with h673 | h673
              · linarith only [h673, hc16, hlam, hphi, p0_1, u1ehi3]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h675 | h675
                · rcases m.htr 0 1 3 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h677 | h677
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h679 | h679
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h680 | h680
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h681 | h681
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h682 | h682
                              · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h684 | h684
                                  · linarith only [h665, h684, hlam]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h687 | h687
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h688 | h688
                                        · linarith only [h667, h688, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h690 | h690
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h691 | h691
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h693 | h693
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h694 | h694
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h695 | h695
                                                    · linarith only [h683, h684, h688, h690, h694, h695, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi5]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h697 | h697
                                                      · linarith only [h675, h679, h680, h683, h684, h695, h697, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · linarith only [h688, h690, h697, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h700 | h700
                                                    · linarith only [h683, h684, h700, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h702 | h702
                                                      · linarith only [h675, h679, h680, h683, h684, h700, h702, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · linarith only [h675, h679, h680, h683, h684, h690, h700, h702, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                · linarith only [h673, h693, hlam]
                                              · linarith only [h671, h692, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h707 | h707
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h708 | h708
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h709 | h709
                                                  · linarith only [h690, h691, h709, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h711 | h711
                                                    · linarith only [h683, h684, h711, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h713 | h713
                                                      · linarith only [h675, h679, h680, h683, h684, h711, h713, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · linarith only [h675, h679, h680, h684, h687, h690, h691, h711, h713, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                · linarith only [h673, h708, hlam]
                                              · linarith only [h671, h707, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h718 | h718
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h719 | h719
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h720 | h720
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h721 | h721
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h722 | h722
                                                    · linarith only [h683, h684, h722, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h724 | h724
                                                      · linarith only [h675, h679, h680, h683, h684, h690, h718, h722, h724, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h726 | h726
                                                        · linarith only [h675, h679, h680, h684, h686, h722, h724, h726, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · linarith only [h690, h718, h726, hc23, hc35, hlam, hphi]
                                                  · linarith only [h690, h718, h721, hlam]
                                                · linarith only [h673, h720, hlam]
                                              · linarith only [h671, h719, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h732 | h732
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h733 | h733
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h734 | h734
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                                                    · linarith only [h683, h684, h735, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h737 | h737
                                                      · linarith only [h675, h679, h680, h683, h684, h690, h735, h737, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h739 | h739
                                                        · linarith only [h675, h679, h680, h684, h686, h718, h735, h737, h739, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h741 | h741
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h742 | h742
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h743 | h743
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h744 | h744
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h745 | h745
                                                                  · linarith only [h732, h745, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                                  · linarith only [h675, h679, h680, h684, h686, h734, h735, h745, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                                · linarith only [h675, h679, h680, h684, h686, h734, h735, h744, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                              · linarith only [h684, h687, h735, h741, h743, hlam]
                                                            · linarith only [h684, h686, h735, h737, h742, hc23, hc45, hlam, hphi, ht34]
                                                          · linarith only [h684, h686, h718, h734, h741, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                                                    · linarith only [h683, h684, h752, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h754 | h754
                                                      · linarith only [h675, h679, h680, h683, h684, h690, h752, h754, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h756 | h756
                                                        · linarith only [h675, h679, h680, h684, h686, h718, h752, h754, h756, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h758 | h758
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h759 | h759
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h760 | h760
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h761 | h761
                                                                · linarith only [h690, h734, h761, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                                                                · linarith only [h690, h761, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2]
                                                              · linarith only [h684, h687, h752, h758, h760, hlam]
                                                            · linarith only [h684, h732, h752, h759, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                          · linarith only [h684, h687, h690, h734, h758, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                · linarith only [h673, h733, hlam]
                                              · linarith only [h671, h732, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                                        · linarith only [h667, h769, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h772 | h772
                                            · linarith only [h683, h687, h772, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h774 | h774
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h775 | h775
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h776 | h776
                                                  · linarith only [h683, h687, h771, h776, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                                                    · linarith only [h683, h684, h778, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
                                                      · linarith only [h675, h679, h680, h683, h684, h778, h780, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · linarith only [h771, h772, h780, hc23, hc36, hlam, hphi]
                                                · linarith only [h673, h775, hlam]
                                              · linarith only [h671, h774, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h785 | h785
                                            · linarith only [h686, h687, h771, h785, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h787 | h787
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h788 | h788
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h789 | h789
                                                  · linarith only [h686, h687, h789, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h791 | h791
                                                    · linarith only [h683, h687, h788, h791, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h793 | h793
                                                      · linarith only [h675, h679, h680, h683, h684, h771, h791, h793, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h795 | h795
                                                        · linarith only [h675, h679, h680, h684, h686, h785, h791, h793, h795, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h797 | h797
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h799 | h799
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h800 | h800
                                                                · linarith only [h789, h800, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                                · linarith only [h771, h800, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2]
                                                              · linarith only [h686, h687, h791, h793, h797, h799, hc23, hc46, hlam, hphi, ht34]
                                                            · linarith only [h686, h687, h771, h791, h797, h798, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                          · linarith only [h788, h797, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                · linarith only [h673, h788, hlam]
                                              · linarith only [h671, h787, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h808 | h808
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
                                        · linarith only [h667, h809, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h811 | h811
                                          · linarith only [h683, h686, h811, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h813 | h813
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h814 | h814
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h815 | h815
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h816 | h816
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h817 | h817
                                                    · linarith only [h809, h813, h817, hc23, hlam, hphi, ht12, u1ehi5]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h819 | h819
                                                      · linarith only [h683, h811, h813, h819, hc12, hlam, hphi, u1ehi5]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h821 | h821
                                                        · linarith only [h675, h679, h680, h683, h684, h817, h821, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · linarith only [h809, h813, h821, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h686, h808, h816, hlam]
                                                · linarith only [h673, h815, hlam]
                                              · linarith only [h671, h814, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h827 | h827
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h828 | h828
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h829 | h829
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                                                    · linarith only [h683, h684, h830, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h832 | h832
                                                      · linarith only [h675, h679, h680, h683, h684, h830, h832, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h834 | h834
                                                        · linarith only [h675, h679, h680, h683, h684, h813, h830, h834, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h836 | h836
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h837 | h837
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h838 | h838
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h839 | h839
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h840 | h840
                                                                  · linarith only [h827, h840, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                                  · linarith only [h827, h829, h840, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                · linarith only [h686, h827, h829, h832, h839, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                              · linarith only [h684, h808, h813, h830, h838, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                            · linarith only [h684, h808, h813, h830, h837, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                          · linarith only [h684, h808, h813, h836, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                  · linarith only [h686, h808, h829, hlam]
                                                · linarith only [h673, h828, hlam]
                                              · linarith only [h671, h827, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h850 | h850
                                        · linarith only [h667, h850, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h852 | h852
                                          · linarith only [h683, h686, h852, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h854 | h854
                                            · linarith only [h683, h808, h854, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h856 | h856
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h857 | h857
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h858 | h858
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h859 | h859
                                                    · linarith only [h683, h684, h859, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h861 | h861
                                                      · linarith only [h683, h808, h852, h856, h858, h861, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h863 | h863
                                                        · linarith only [h683, h808, h854, h856, h858, h863, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h865 | h865
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h866 | h866
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h867 | h867
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h868 | h868
                                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h869 | h869
                                                                  · linarith only [h856, h869, hc01, hc56, hlam, hphi, ht0b, ht6b, p0_1]
                                                                  · linarith only [h856, h858, h869, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                                · linarith only [h856, h858, h868, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                              · linarith only [h683, h684, h859, h867, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                            · linarith only [h683, h808, h859, h865, h866, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                          · linarith only [h857, h865, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h876 | h876
                                                    · linarith only [h683, h684, h876, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h878 | h878
                                                      · linarith only [h683, h686, h857, h858, h878, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h880 | h880
                                                        · linarith only [h683, h686, h857, h858, h880, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h882 | h882
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h883 | h883
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h884 | h884
                                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h885 | h885
                                                                · linarith only [h858, h885, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                                · linarith only [h852, h885, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2]
                                                              · linarith only [h808, h857, h876, h882, h884, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1]
                                                            · linarith only [h683, h808, h856, h876, h882, h883, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                          · linarith only [h857, h882, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                · linarith only [h673, h857, hlam]
                                              · linarith only [h671, h856, hlam]
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h893 | h893
                                  · linarith only [h665, h893, hlam]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h895 | h895
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h896 | h896
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h897 | h897
                                        · linarith only [h667, h897, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h900 | h900
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h902 | h902
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h903 | h903
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h904 | h904
                                                    · linarith only [h683, h895, h897, h903, h904, hc23, hlam, hphi, ht12, u1ehi5]
                                                    · linarith only [h683, h895, h903, h904, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h907 | h907
                                                    · linarith only [h675, h679, h683, h895, h897, h907, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                                                    · linarith only [h683, h896, h903, h907, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                                · linarith only [h673, h902, hlam]
                                              · linarith only [h671, h901, hlam]
                                            · linarith only [h683, h896, h900, hlam]
                                          · linarith only [h683, h895, h899, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                                        · linarith only [h667, h914, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h916 | h916
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h917 | h917
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h918 | h918
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h919 | h919
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h920 | h920
                                                  · linarith only [h895, h896, h920, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
                                                    · linarith only [h896, h914, h917, h922, hc23, hlam, hphi, ht12, u1ehi1]
                                                    · linarith only [h675, h679, h680, h683, h895, h922, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi4]
                                                · linarith only [h673, h919, hlam]
                                              · linarith only [h671, h918, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h928 | h928
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h929 | h929
                                                  · linarith only [h683, h895, h917, h929, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h931 | h931
                                                    · linarith only [h683, h895, h914, h931, hc23, hlam, hphi, ht12, u1ehi4]
                                                    · linarith only [h675, h679, h680, h683, h895, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi4]
                                                · linarith only [h673, h928, hlam]
                                              · linarith only [h671, h927, hlam]
                                          · linarith only [h683, h895, h916, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h937 | h937
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h938 | h938
                                        · linarith only [h667, h938, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h941 | h941
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h942 | h942
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h943 | h943
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h944 | h944
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h945 | h945
                                                    · linarith only [h895, h938, h940, h945, hc23, hlam, hphi, ht12, u1ehi1]
                                                    · linarith only [h683, h937, h945, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h895, h937, h944, hlam]
                                                · linarith only [h673, h943, hlam]
                                              · linarith only [h671, h942, hlam]
                                            · linarith only [h895, h937, h940, h941, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h952 | h952
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h953 | h953
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h954 | h954
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h955 | h955
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h956 | h956
                                                    · linarith only [h938, h956, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h683, h937, h956, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h683, h937, h940, h955, hlam]
                                                · linarith only [h673, h954, hlam]
                                              · linarith only [h671, h953, hlam]
                                            · linarith only [h683, h937, h952, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h963 | h963
                                        · linarith only [h667, h963, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h965 | h965
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h966 | h966
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h968 | h968
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h969 | h969
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h970 | h970
                                                    · linarith only [h675, h679, h963, h965, h970, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                    · linarith only [h675, h679, h680, h683, h970, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h973 | h973
                                                    · linarith only [h675, h679, h963, h966, h973, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                    · linarith only [h683, h973, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                · linarith only [h673, h968, hlam]
                                              · linarith only [h671, h967, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h978 | h978
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h979 | h979
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h980 | h980
                                                  · linarith only [h965, h966, h980, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h982 | h982
                                                    · linarith only [h675, h679, h963, h982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                    · linarith only [h675, h679, h680, h683, h982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                · linarith only [h673, h979, hlam]
                                              · linarith only [h671, h978, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h987 | h987
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h988 | h988
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h989 | h989
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h990 | h990
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h991 | h991
                                                    · linarith only [h675, h679, h963, h987, h991, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                    · linarith only [h675, h679, h680, h683, h991, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                  · linarith only [h965, h987, h990, hlam]
                                                · linarith only [h673, h989, hlam]
                                              · linarith only [h671, h988, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h998 | h998
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h999 | h999
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1000 | h1000
                                                    · linarith only [h1000, h963, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h1000, h683, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1003 | h1003
                                                    · linarith only [h1003, h675, h679, h683, h963, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                    · linarith only [h1003, h683, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                · linarith only [h673, h998, hlam]
                                              · linarith only [h671, h997, hlam]
                              · linarith only [h682, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h681, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h680, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h679, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h671, h678, hlam, p0_1]
                    · linarith only [h677, hlam, p0_0]
                  · linarith only [h667, h676, hlam, p0_1]
                · linarith only [h675, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h664, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1017 | h1017
    · rcases p0_3 (m.d 1 2) (by simp) with h1018 | h1018
      · linarith only [h1018, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h1020 | h1020
        · linarith only [h1020, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h1022 | h1022
          · linarith only [h1022, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h1024 | h1024
            · linarith only [h1024, hlam, p0_0]
            · rcases p0_3 (m.d 1 6) (by simp) with h1026 | h1026
              · linarith only [h1026, hc16, hlam, hphi, p0_1, u1ehi4]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1028 | h1028
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1029 | h1029
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1030 | h1030
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1031 | h1031
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1032 | h1032
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h1033 | h1033
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h1034 | h1034
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h1035 | h1035
                              · rcases m.htr 1 2 3 (by decide) (by decide) with h1036 | h1036
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h1037 | h1037
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1038 | h1038
                                    · linarith only [h1018, h1038, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1040 | h1040
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1042 | h1042
                                          · linarith only [h1020, h1042, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1044 | h1044
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1045 | h1045
                                              · linarith only [h1022, h1045, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1047 | h1047
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1048 | h1048
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1049 | h1049
                                                    · linarith only [h1036, h1038, h1049, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1036, h1038, h1041, h1049, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h1026, h1048, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1053 | h1053
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1054 | h1054
                                                    · linarith only [h1036, h1038, h1054, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1036, h1038, h1041, h1054, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h1026, h1053, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1058 | h1058
                                              · linarith only [h1022, h1058, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1060 | h1060
                                                · linarith only [h1041, h1044, h1060, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1062 | h1062
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                                                    · linarith only [h1036, h1038, h1063, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1038, h1040, h1041, h1044, h1063, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h1026, h1062, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1067 | h1067
                                          · linarith only [h1020, h1067, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1069 | h1069
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1070 | h1070
                                              · linarith only [h1022, h1070, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1072 | h1072
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1073 | h1073
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                                                    · linarith only [h1041, h1069, h1074, hc23, hlam, hphi, ht12, u1ehi5]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1076 | h1076
                                                      · linarith only [h1037, h1038, h1074, h1076, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1078 | h1078
                                                        · linarith only [h1028, h1032, h1034, h1037, h1038, h1074, h1076, h1078, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · linarith only [h1041, h1069, h1078, hc23, hc34, hlam, hphi]
                                                  · linarith only [h1026, h1073, hlam]
                                                · linarith only [h1041, h1069, h1072, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1083 | h1083
                                              · linarith only [h1022, h1083, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1085 | h1085
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1086 | h1086
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1087 | h1087
                                                    · linarith only [h1036, h1038, h1087, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1089 | h1089
                                                      · linarith only [h1037, h1038, h1087, h1089, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1091 | h1091
                                                        · linarith only [h1028, h1032, h1034, h1037, h1038, h1069, h1087, h1089, h1091, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1093 | h1093
                                                          · linarith only [h1028, h1032, h1034, h1037, h1038, h1089, h1093, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                          · linarith only [h1028, h1032, h1034, h1037, h1038, h1085, h1087, h1089, h1093, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                  · linarith only [h1026, h1086, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1097 | h1097
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1098 | h1098
                                                    · linarith only [h1041, h1098, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1100 | h1100
                                                      · linarith only [h1037, h1038, h1098, h1100, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1102 | h1102
                                                        · linarith only [h1028, h1032, h1034, h1037, h1038, h1069, h1098, h1100, h1102, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1104 | h1104
                                                          · linarith only [h1028, h1032, h1034, h1037, h1038, h1085, h1100, h1104, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1106 | h1106
                                                            · linarith only [h1041, h1083, h1106, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h1028, h1032, h1033, h1035, h1041, h1106, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                  · linarith only [h1026, h1097, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1110 | h1110
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1111 | h1111
                                          · linarith only [h1020, h1111, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1113 | h1113
                                            · linarith only [h1036, h1040, h1113, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1115 | h1115
                                              · linarith only [h1022, h1115, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1117 | h1117
                                                · linarith only [h1037, h1040, h1117, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1119 | h1119
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
                                                    · linarith only [h1036, h1038, h1120, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1036, h1040, h1110, h1119, h1120, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h1026, h1119, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1124 | h1124
                                          · linarith only [h1020, h1124, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1126 | h1126
                                            · linarith only [h1037, h1040, h1110, h1126, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                                              · linarith only [h1022, h1128, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1130 | h1130
                                                · linarith only [h1037, h1040, h1130, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1132 | h1132
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                                                    · linarith only [h1110, h1133, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1135 | h1135
                                                      · linarith only [h1037, h1040, h1132, h1133, h1135, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1137 | h1137
                                                        · linarith only [h1028, h1032, h1034, h1037, h1038, h1126, h1133, h1135, h1137, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1139 | h1139
                                                          · linarith only [h1028, h1032, h1034, h1037, h1038, h1130, h1135, h1139, hc01, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1141 | h1141
                                                            · linarith only [h1110, h1128, h1141, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h1028, h1032, h1033, h1035, h1110, h1141, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                  · linarith only [h1026, h1132, hlam]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1145 | h1145
                                    · linarith only [h1018, h1145, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1147 | h1147
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                                        · linarith only [h1036, h1037, h1148, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1150 | h1150
                                          · linarith only [h1020, h1150, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1152 | h1152
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1153 | h1153
                                              · linarith only [h1022, h1153, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1155 | h1155
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1156 | h1156
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1157 | h1157
                                                    · linarith only [h1148, h1157, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1159 | h1159
                                                      · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1153, h1159, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1161 | h1161
                                                        · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1153, h1161, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · linarith only [h1150, h1152, h1161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                                  · linarith only [h1026, h1156, hlam]
                                                · linarith only [h1036, h1037, h1152, h1155, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1166 | h1166
                                              · linarith only [h1022, h1166, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1168 | h1168
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1169 | h1169
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1170 | h1170
                                                    · linarith only [h1036, h1145, h1170, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1172 | h1172
                                                      · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1150, h1166, h1172, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1174 | h1174
                                                        · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1152, h1166, h1174, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1176 | h1176
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1177 | h1177
                                                            · linarith only [h1037, h1147, h1166, h1174, h1177, hc23, hc34, hlam, hphi]
                                                            · linarith only [h1028, h1032, h1033, h1035, h1148, h1177, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                          · linarith only [h1037, h1147, h1174, h1176, hc23, hc46, hlam, hphi, ht34]
                                                  · linarith only [h1026, h1169, hlam]
                                                · linarith only [h1037, h1147, h1168, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1183 | h1183
                                        · linarith only [h1036, h1037, h1183, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1185 | h1185
                                          · linarith only [h1020, h1185, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1187 | h1187
                                            · linarith only [h1036, h1147, h1187, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                                              · linarith only [h1022, h1189, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1191 | h1191
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1192 | h1192
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1193 | h1193
                                                    · linarith only [h1183, h1193, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1195 | h1195
                                                      · linarith only [h1036, h1185, h1195, hc12, hlam, hphi, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1197 | h1197
                                                        · linarith only [h1028, h1032, h1033, h1035, h1036, h1147, h1187, h1189, h1191, h1197, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1199 | h1199
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1200 | h1200
                                                            · linarith only [h1028, h1032, h1033, h1036, h1147, h1189, h1191, h1200, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                            · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1193, h1200, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                          · linarith only [h1036, h1037, h1191, h1199, hc14, hlam, hphi, u1ehi2]
                                                  · linarith only [h1026, h1192, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1205 | h1205
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1206 | h1206
                                                    · linarith only [h1036, h1145, h1206, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1208 | h1208
                                                      · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1189, h1208, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1210 | h1210
                                                        · linarith only [h1028, h1032, h1033, h1035, h1036, h1037, h1189, h1210, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1212 | h1212
                                                          · linarith only [h1036, h1037, h1191, h1206, h1212, hc23, hc34, hlam, hphi]
                                                          · linarith only [h1036, h1037, h1212, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                  · linarith only [h1026, h1205, hlam]
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h1216 | h1216
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1217 | h1217
                                    · linarith only [h1018, h1217, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1219 | h1219
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1220 | h1220
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1221 | h1221
                                          · linarith only [h1020, h1221, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1223 | h1223
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1224 | h1224
                                              · linarith only [h1022, h1224, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1226 | h1226
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1227 | h1227
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1228 | h1228
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1229 | h1229
                                                      · linarith only [h1036, h1216, h1221, h1226, h1229, hc23, hlam, hphi, ht12, u1ehi5]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1216, h1226, h1229, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                                                    · linarith only [h1036, h1216, h1226, h1228, hc34, hlam, hphi, ht12, ht23, u1ehi5]
                                                  · linarith only [h1026, h1227, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1234 | h1234
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1235 | h1235
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1236 | h1236
                                                      · linarith only [h1036, h1221, h1236, hc23, hlam, hphi, ht12, u1ehi1]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1219, h1226, h1236, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi3]
                                                    · linarith only [h1036, h1219, h1226, h1235, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                  · linarith only [h1026, h1234, hlam]
                                            · linarith only [h1036, h1219, h1223, hlam]
                                        · linarith only [h1036, h1216, h1220, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1244 | h1244
                                          · linarith only [h1020, h1244, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1246 | h1246
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1247 | h1247
                                              · linarith only [h1022, h1247, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1249 | h1249
                                                · linarith only [h1216, h1219, h1249, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1251 | h1251
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1252 | h1252
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1253 | h1253
                                                      · linarith only [h1219, h1244, h1246, h1253, hc23, hlam, hphi, ht12, u1ehi1]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1216, h1253, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi3]
                                                    · linarith only [h1036, h1216, h1252, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                  · linarith only [h1026, h1251, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1258 | h1258
                                              · linarith only [h1022, h1258, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1260 | h1260
                                                · linarith only [h1036, h1216, h1246, h1260, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1262 | h1262
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1263 | h1263
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1264 | h1264
                                                      · linarith only [h1036, h1216, h1244, h1264, hc23, hlam, hphi, ht12, u1ehi3]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1216, h1264, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi3]
                                                    · linarith only [h1036, h1216, h1263, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                  · linarith only [h1026, h1262, hlam]
                                        · linarith only [h1036, h1216, h1243, hlam]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1270 | h1270
                                    · linarith only [h1018, h1270, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1272 | h1272
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1273 | h1273
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1274 | h1274
                                          · linarith only [h1020, h1274, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1276 | h1276
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1277 | h1277
                                              · linarith only [h1022, h1277, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1279 | h1279
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1280 | h1280
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1282 | h1282
                                                      · linarith only [h1216, h1272, h1273, h1274, h1282, hc23, hlam, hphi, ht12, u1ehi5]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1272, h1282, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                                                    · linarith only [h1036, h1272, h1273, h1281, hc13, hlam, hphi, u1ehi5]
                                                  · linarith only [h1026, h1280, hlam]
                                                · linarith only [h1216, h1272, h1279, hlam]
                                            · linarith only [h1036, h1272, h1276, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1289 | h1289
                                          · linarith only [h1020, h1289, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1291 | h1291
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1292 | h1292
                                              · linarith only [h1022, h1292, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1294 | h1294
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1295 | h1295
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1296 | h1296
                                                    · linarith only [h1036, h1273, h1296, hc23, hlam, hphi, ht12, u1ehi1]
                                                    · linarith only [h1028, h1032, h1033, h1036, h1272, h1296, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi5]
                                                  · linarith only [h1026, h1295, hlam]
                                                · linarith only [h1036, h1272, h1273, h1294, hlam]
                                            · linarith only [h1036, h1272, h1291, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1303 | h1303
                                          · linarith only [h1020, h1303, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1305 | h1305
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1306 | h1306
                                              · linarith only [h1022, h1306, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1308 | h1308
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1309 | h1309
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1310 | h1310
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1311 | h1311
                                                      · linarith only [h1272, h1302, h1303, h1308, h1311, hc23, hlam, hphi, ht12, u1ehi1]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1311, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                    · linarith only [h1036, h1302, h1310, hc13, hlam, hphi, u1ehi1]
                                                  · linarith only [h1026, h1309, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1316 | h1316
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1318 | h1318
                                                      · linarith only [h1303, h1318, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1318, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                    · linarith only [h1036, h1302, h1317, hc13, hlam, hphi, u1ehi1]
                                                  · linarith only [h1026, h1316, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1323 | h1323
                                              · linarith only [h1022, h1323, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1325 | h1325
                                                · linarith only [h1302, h1305, h1325, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1327 | h1327
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1328 | h1328
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1329 | h1329
                                                      · linarith only [h1303, h1329, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · linarith only [h1028, h1032, h1034, h1036, h1329, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                    · linarith only [h1036, h1328, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · linarith only [h1026, h1327, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1334 | h1334
                                          · linarith only [h1020, h1334, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1336 | h1336
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1337 | h1337
                                              · linarith only [h1022, h1337, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1339 | h1339
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1340 | h1340
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1341 | h1341
                                                    · linarith only [h1302, h1341, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h1036, h1341, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · linarith only [h1026, h1340, hlam]
                                                · linarith only [h1302, h1336, h1339, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1346 | h1346
                                              · linarith only [h1022, h1346, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1348 | h1348
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1349 | h1349
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1350 | h1350
                                                    · linarith only [h1302, h1350, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h1036, h1350, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · linarith only [h1026, h1349, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1354 | h1354
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1355 | h1355
                                                    · linarith only [h1028, h1032, h1036, h1302, h1355, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                    · linarith only [h1036, h1355, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                                  · linarith only [h1026, h1354, hlam]
                              · linarith only [h1035, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h1034, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h1033, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h1032, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h1031, hlam, p0_0]
                    · linarith only [h1022, h1030, hlam, p0_1]
                  · linarith only [h1020, h1029, hlam, p0_1]
                · linarith only [h1028, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h1017, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1368 | h1368
    · rcases p0_3 (m.d 1 2) (by simp) with h1369 | h1369
      · linarith only [h1369, hc12, hlam, hphi, p0_1, u1ehi5]
      · rcases p0_3 (m.d 1 3) (by simp) with h1371 | h1371
        · linarith only [h1371, hc13, hlam, hphi, p0_1, u1ehi5]
        · rcases p0_3 (m.d 1 4) (by simp) with h1373 | h1373
          · linarith only [h1373, hc14, hlam, hphi, p0_1, u1ehi5]
          · rcases p0_3 (m.d 1 5) (by simp) with h1375 | h1375
            · linarith only [h1375, hc15, hlam, hphi, p0_1, u1ehi5]
            · rcases p0_3 (m.d 1 6) (by simp) with h1377 | h1377
              · linarith only [h1377, hlam, p0_0]
              · rcases m.htr 0 1 2 (by decide) (by decide) with h1379 | h1379
                · rcases m.htr 0 1 3 (by decide) (by decide) with h1380 | h1380
                  · rcases m.htr 0 1 4 (by decide) (by decide) with h1381 | h1381
                    · rcases m.htr 0 1 5 (by decide) (by decide) with h1382 | h1382
                      · rcases m.htr 0 2 3 (by decide) (by decide) with h1383 | h1383
                        · rcases m.htr 0 3 4 (by decide) (by decide) with h1384 | h1384
                          · rcases m.htr 0 3 5 (by decide) (by decide) with h1385 | h1385
                            · rcases m.htr 0 4 5 (by decide) (by decide) with h1386 | h1386
                              · rcases m.htr 1 2 3 (by decide) (by decide) with h1387 | h1387
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h1388 | h1388
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1389 | h1389
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1390 | h1390
                                      · linarith only [h1369, h1390, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1392 | h1392
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1393 | h1393
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1394 | h1394
                                            · linarith only [h1371, h1394, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1396 | h1396
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1397 | h1397
                                                · linarith only [h1373, h1397, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1399 | h1399
                                                  · linarith only [h1375, h1399, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1401 | h1401
                                                    · linarith only [h1387, h1390, h1401, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1387, h1390, h1392, h1401, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1404 | h1404
                                                · linarith only [h1373, h1404, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1406 | h1406
                                                  · linarith only [h1375, h1406, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1408 | h1408
                                                    · linarith only [h1387, h1390, h1408, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1387, h1390, h1392, h1408, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1411 | h1411
                                            · linarith only [h1371, h1411, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1413 | h1413
                                              · linarith only [h1392, h1393, h1413, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1415 | h1415
                                                · linarith only [h1373, h1415, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1417 | h1417
                                                  · linarith only [h1375, h1417, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1419 | h1419
                                                    · linarith only [h1387, h1390, h1419, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · linarith only [h1389, h1390, h1392, h1393, h1419, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1422 | h1422
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1423 | h1423
                                            · linarith only [h1371, h1423, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1425 | h1425
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1426 | h1426
                                                · linarith only [h1373, h1426, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1428 | h1428
                                                  · linarith only [h1375, h1428, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1430 | h1430
                                                    · linarith only [h1392, h1430, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1432 | h1432
                                                      · linarith only [h1388, h1390, h1430, h1432, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · linarith only [h1392, h1422, h1432, hc23, hc34, hlam, hphi]
                                              · linarith only [h1392, h1422, h1425, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1436 | h1436
                                            · linarith only [h1371, h1436, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1438 | h1438
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1439 | h1439
                                                · linarith only [h1373, h1439, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1441 | h1441
                                                  · linarith only [h1375, h1441, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1443 | h1443
                                                    · linarith only [h1387, h1390, h1443, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1445 | h1445
                                                      · linarith only [h1422, h1445, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1447 | h1447
                                                        · linarith only [h1388, h1390, h1443, h1447, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1449 | h1449
                                                          · linarith only [h1388, h1390, h1449, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1451 | h1451
                                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h1452 | h1452
                                                              · linarith only [h1388, h1390, h1443, h1449, h1452, hc23, hc34, hlam, hphi]
                                                              · linarith only [h1392, h1452, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                                            · linarith only [h1392, h1451, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1456 | h1456
                                                · linarith only [h1373, h1456, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1458 | h1458
                                                  · linarith only [h1375, h1458, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1460 | h1460
                                                    · linarith only [h1392, h1460, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1462 | h1462
                                                      · linarith only [h1388, h1422, h1460, h1462, hc12, hlam, hphi, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1464 | h1464
                                                        · linarith only [h1388, h1390, h1460, h1464, hc01, hc36, hlam, hphi, ht0b, ht6b, p0_1]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1466 | h1466
                                                          · linarith only [h1388, h1390, h1466, hc01, hc46, hlam, hphi, ht0b, ht6b, p0_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1468 | h1468
                                                            · linarith only [h1438, h1468, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                            · linarith only [h1379, h1383, h1384, h1386, h1392, h1468, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1471 | h1471
                                      · linarith only [h1369, h1471, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1473 | h1473
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1474 | h1474
                                          · linarith only [h1387, h1389, h1474, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1476 | h1476
                                            · linarith only [h1371, h1476, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1478 | h1478
                                              · linarith only [h1388, h1389, h1478, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1480 | h1480
                                                · linarith only [h1373, h1480, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1482 | h1482
                                                  · linarith only [h1375, h1482, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1484 | h1484
                                                    · linarith only [h1387, h1389, h1482, h1484, hc34, hc56, hlam, hphi, ht45]
                                                    · linarith only [h1387, h1389, h1473, h1482, h1484, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1487 | h1487
                                          · linarith only [h1388, h1389, h1473, h1487, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1489 | h1489
                                            · linarith only [h1371, h1489, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1491 | h1491
                                              · linarith only [h1388, h1389, h1491, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1493 | h1493
                                                · linarith only [h1373, h1493, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1495 | h1495
                                                  · linarith only [h1375, h1495, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1497 | h1497
                                                    · linarith only [h1473, h1497, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1499 | h1499
                                                      · linarith only [h1388, h1389, h1487, h1495, h1497, h1499, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1501 | h1501
                                                        · linarith only [h1379, h1383, h1385, h1388, h1389, h1497, h1499, h1501, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1503 | h1503
                                                          · linarith only [h1379, h1383, h1385, h1388, h1389, h1499, h1503, hc01, hc46, hlam, hphi, ht0b, ht6b]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                                                            · linarith only [h1491, h1505, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                                            · linarith only [h1379, h1383, h1384, h1386, h1473, h1505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1508 | h1508
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1509 | h1509
                                      · linarith only [h1369, h1509, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
                                        · linarith only [h1387, h1388, h1511, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1513 | h1513
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1514 | h1514
                                            · linarith only [h1371, h1514, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1516 | h1516
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1517 | h1517
                                                · linarith only [h1373, h1517, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1519 | h1519
                                                  · linarith only [h1375, h1519, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1521 | h1521
                                                    · linarith only [h1511, h1521, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1523 | h1523
                                                      · linarith only [h1387, h1509, h1523, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b, p0_1]
                                                      · linarith only [h1379, h1383, h1384, h1387, h1388, h1513, h1521, h1523, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                              · linarith only [h1387, h1388, h1513, h1516, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1527 | h1527
                                            · linarith only [h1371, h1527, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1529 | h1529
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1530 | h1530
                                                · linarith only [h1373, h1530, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1532 | h1532
                                                  · linarith only [h1375, h1532, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1534 | h1534
                                                    · linarith only [h1387, h1509, h1534, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1536 | h1536
                                                      · linarith only [h1379, h1383, h1384, h1387, h1388, h1513, h1534, h1536, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1538 | h1538
                                                        · linarith only [h1379, h1383, h1384, h1388, h1508, h1534, h1536, h1538, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1540 | h1540
                                                          · linarith only [h1379, h1383, h1384, h1388, h1508, h1530, h1534, h1536, h1540, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                                                          · linarith only [h1388, h1508, h1513, h1540, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                              · linarith only [h1388, h1508, h1529, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1544 | h1544
                                      · linarith only [h1369, h1544, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1546 | h1546
                                        · linarith only [h1387, h1388, h1546, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1548 | h1548
                                          · linarith only [h1387, h1508, h1548, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1550 | h1550
                                            · linarith only [h1371, h1550, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1552 | h1552
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1553 | h1553
                                                · linarith only [h1373, h1553, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1555 | h1555
                                                  · linarith only [h1375, h1555, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1557 | h1557
                                                    · linarith only [h1546, h1557, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1559 | h1559
                                                      · linarith only [h1387, h1548, h1559, hc12, hlam, hphi, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1561 | h1561
                                                        · linarith only [h1379, h1383, h1384, h1387, h1388, h1557, h1561, hc01, hc36, hlam, hphi, ht0b, ht6b]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1563 | h1563
                                                          · linarith only [h1379, h1383, h1384, h1552, h1553, h1557, h1563, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                                                          · linarith only [h1387, h1388, h1563, hc23, hc46, hlam, hphi, ht34]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1566 | h1566
                                                · linarith only [h1373, h1566, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1568 | h1568
                                                  · linarith only [h1375, h1568, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
                                                    · linarith only [h1387, h1544, h1570, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1]
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1572 | h1572
                                                      · linarith only [h1379, h1383, h1384, h1386, h1387, h1388, h1548, h1552, h1572, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1574 | h1574
                                                        · linarith only [h1379, h1383, h1384, h1386, h1387, h1388, h1550, h1552, h1574, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi2]
                                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h1576 | h1576
                                                          · linarith only [h1387, h1388, h1566, h1570, h1576, hc23, hc34, hlam, hphi]
                                                          · linarith only [h1387, h1388, h1576, hc46, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                · rcases m.htr 1 2 4 (by decide) (by decide) with h1579 | h1579
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1580 | h1580
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1581 | h1581
                                      · linarith only [h1369, h1581, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1583 | h1583
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1584 | h1584
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1585 | h1585
                                            · linarith only [h1371, h1585, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1587 | h1587
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1588 | h1588
                                                · linarith only [h1373, h1588, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1590 | h1590
                                                  · linarith only [h1375, h1590, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1592 | h1592
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1593 | h1593
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1594 | h1594
                                                        · linarith only [h1383, h1387, h1579, h1585, h1594, hc02, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                                                        · linarith only [h1387, h1579, h1587, h1594, hc36, hlam, hphi, ht12, ht23, u1ehi4]
                                                      · linarith only [h1387, h1579, h1587, h1593, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                    · linarith only [h1387, h1579, h1587, h1592, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1599 | h1599
                                                · linarith only [h1373, h1599, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1601 | h1601
                                                  · linarith only [h1375, h1601, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1603 | h1603
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1604 | h1604
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1605 | h1605
                                                        · linarith only [h1387, h1585, h1605, hc23, hlam, hphi, ht12, u1ehi1]
                                                        · linarith only [h1387, h1580, h1587, h1605, hc36, hlam, hphi, ht12, ht23, u1ehi3]
                                                      · linarith only [h1387, h1580, h1587, h1604, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                                    · linarith only [h1387, h1580, h1587, h1603, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                          · linarith only [h1387, h1580, h1584, hlam]
                                        · linarith only [h1387, h1579, h1583, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1612 | h1612
                                      · linarith only [h1369, h1612, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1614 | h1614
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1615 | h1615
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1616 | h1616
                                            · linarith only [h1371, h1616, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1618 | h1618
                                              · linarith only [h1579, h1580, h1618, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1620 | h1620
                                                · linarith only [h1373, h1620, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1622 | h1622
                                                  · linarith only [h1375, h1622, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1624 | h1624
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1625 | h1625
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1626 | h1626
                                                        · linarith only [h1580, h1615, h1616, h1626, hc23, hlam, hphi, ht12, u1ehi1]
                                                        · linarith only [h1387, h1579, h1626, hc36, hlam, hphi, ht12, ht23, u1ehi3]
                                                      · linarith only [h1387, h1579, h1615, h1625, hc13, hlam, hphi, u1ehi3]
                                                    · linarith only [h1387, h1579, h1624, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1631 | h1631
                                            · linarith only [h1371, h1631, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1633 | h1633
                                              · linarith only [h1387, h1579, h1615, h1633, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1635 | h1635
                                                · linarith only [h1373, h1635, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1637 | h1637
                                                  · linarith only [h1375, h1637, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1639 | h1639
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1640 | h1640
                                                      · linarith only [h1387, h1579, h1615, h1640, hc23, hlam, hphi, ht12, u1ehi3]
                                                      · linarith only [h1379, h1383, h1385, h1387, h1579, h1640, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi3]
                                                    · linarith only [h1387, h1579, h1639, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                        · linarith only [h1387, h1579, h1614, hlam]
                                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1645 | h1645
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1646 | h1646
                                      · linarith only [h1369, h1646, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1648 | h1648
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1649 | h1649
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1650 | h1650
                                            · linarith only [h1371, h1650, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1652 | h1652
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1653 | h1653
                                                · linarith only [h1373, h1653, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1655 | h1655
                                                  · linarith only [h1375, h1655, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1657 | h1657
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1658 | h1658
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1659 | h1659
                                                        · linarith only [h1579, h1648, h1650, h1659, hc23, hlam, hphi, ht12, u1ehi1]
                                                        · linarith only [h1387, h1645, h1659, hc36, hlam, hphi, ht12, ht23, u1ehi4]
                                                      · linarith only [h1579, h1645, h1657, h1658, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                                                    · linarith only [h1648, h1650, h1657, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                              · linarith only [h1579, h1645, h1652, hlam]
                                          · linarith only [h1387, h1645, h1649, hlam]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1666 | h1666
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1667 | h1667
                                            · linarith only [h1371, h1667, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1669 | h1669
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1670 | h1670
                                                · linarith only [h1373, h1670, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1672 | h1672
                                                  · linarith only [h1375, h1672, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1674 | h1674
                                                    · linarith only [h1387, h1648, h1674, hc23, hlam, hphi, ht12, u1ehi1]
                                                    · linarith only [h1379, h1383, h1384, h1387, h1645, h1674, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi4]
                                              · linarith only [h1579, h1645, h1669, hlam]
                                          · linarith only [h1387, h1645, h1666, hlam]
                                    · rcases m.htr 1 2 6 (by decide) (by decide) with h1679 | h1679
                                      · linarith only [h1369, h1679, hlam]
                                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1681 | h1681
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1682 | h1682
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1683 | h1683
                                            · linarith only [h1371, h1683, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1685 | h1685
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1686 | h1686
                                                · linarith only [h1373, h1686, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1688 | h1688
                                                  · linarith only [h1375, h1688, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1690 | h1690
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1691 | h1691
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1692 | h1692
                                                        · linarith only [h1683, h1692, hc23, hlam, hphi, ht12, u1ehi2]
                                                        · linarith only [h1387, h1692, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h1579, h1682, h1690, h1691, hc13, hlam, hphi, u1ehi1]
                                                    · linarith only [h1379, h1383, h1384, h1387, h1690, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1697 | h1697
                                                · linarith only [h1373, h1697, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1699 | h1699
                                                  · linarith only [h1375, h1699, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1701 | h1701
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1702 | h1702
                                                      · rcases m.htr 2 3 6 (by decide) (by decide) with h1703 | h1703
                                                        · linarith only [h1683, h1703, hc23, hlam, hphi, ht12, u1ehi2]
                                                        · linarith only [h1387, h1703, hc36, hlam, hphi, ht12, ht23, u1ehi1]
                                                      · linarith only [h1579, h1682, h1701, h1702, hc13, hlam, hphi, u1ehi1]
                                                    · linarith only [h1681, h1683, h1701, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1708 | h1708
                                            · linarith only [h1371, h1708, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1710 | h1710
                                              · linarith only [h1681, h1682, h1710, hlam]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1712 | h1712
                                                · linarith only [h1373, h1712, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1714 | h1714
                                                  · linarith only [h1375, h1714, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1716 | h1716
                                                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1717 | h1717
                                                      · linarith only [h1682, h1717, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · linarith only [h1379, h1383, h1385, h1387, h1717, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                                    · linarith only [h1379, h1383, h1385, h1387, h1681, h1682, h1716, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1721 | h1721
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1722 | h1722
                                            · linarith only [h1371, h1722, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1724 | h1724
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1725 | h1725
                                                · linarith only [h1373, h1725, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1727 | h1727
                                                  · linarith only [h1375, h1727, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1729 | h1729
                                                    · linarith only [h1681, h1729, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h1379, h1383, h1384, h1387, h1729, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                              · linarith only [h1681, h1721, h1724, hlam]
                                          · rcases m.htr 1 3 6 (by decide) (by decide) with h1733 | h1733
                                            · linarith only [h1371, h1733, hlam]
                                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1735 | h1735
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1736 | h1736
                                                · linarith only [h1373, h1736, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1738 | h1738
                                                  · linarith only [h1375, h1738, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1740 | h1740
                                                    · linarith only [h1681, h1740, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h1379, h1383, h1384, h1387, h1740, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                                              · rcases m.htr 1 4 6 (by decide) (by decide) with h1743 | h1743
                                                · linarith only [h1373, h1743, hlam]
                                                · rcases m.htr 1 5 6 (by decide) (by decide) with h1745 | h1745
                                                  · linarith only [h1375, h1745, hlam]
                                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1747 | h1747
                                                    · linarith only [h1681, h1747, hc23, hlam, hphi, ht12, u1ehi2]
                                                    · linarith only [h1379, h1383, h1384, h1387, h1747, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u1ehi1]
                              · linarith only [h1386, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                            · linarith only [h1375, h1385, hc01, hc35, hlam, hphi, ht12, ht23, p0_1, u0ehi2, u1ehi4]
                          · linarith only [h1375, h1384, hc01, hc34, hlam, hphi, ht12, ht23, p0_1, u0ehi2, u1ehi4]
                        · linarith only [h1375, h1383, hc01, hc23, hlam, hphi, ht12, p0_1, u0ehi1, u1ehi4]
                      · linarith only [h1375, h1382, hlam, p0_1]
                    · linarith only [h1373, h1381, hlam, p0_1]
                  · linarith only [h1375, h1380, hc13, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h1375, h1379, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h1368, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_H_R_M_LI (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n8l_sAA8_H_R_M_LR (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n8l_sAA8_M_IR_H_I (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_M_IR_H_L (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n8l_sAA8_M_IR_H_R (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 5 6 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 5 6 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h2, h8, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                          · linarith only [h0, h10, h12, h2, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h2, h8, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                          · linarith only [h0, h10, h15, h2, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                      · rcases m.htr 2 5 6 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h10, h19, h2, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h21 | h21
                            · linarith only [h0, h2, h21, h9, hc01, hc56, hlam, hphi, ht0b, ht6b]
                            · linarith only [h0, h18, h21, h3, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h10, h24, h8, hlam]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h26 | h26
                            · linarith only [h0, h18, h2, h26, h5, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                            · rcases m.htr 4 5 6 (by decide) (by decide) with h28 | h28
                              · linarith only [h0, h10, h18, h2, h28, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                              · linarith only [h0, h10, h2, h28, h4, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                    · linarith only [h0, h2, h5, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h0, h2, h32, h4, h8, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 5 6 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h37 | h37
                            · rcases m.htr 4 5 6 (by decide) (by decide) with h38 | h38
                              · linarith only [h0, h2, h34, h38, h4, h8, hc01, hc56, hlam, hphi, ht0b, ht6b]
                              · linarith only [h0, h3, h35, h38, hc01, hc45, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h32, h35, h37, hlam]
                          · linarith only [h0, h2, h36, h4, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h44 | h44
                            · linarith only [h0, h2, h35, h4, h43, h44, hc01, hc25, hlam, hphi, ht0b, ht56, ht6b]
                            · linarith only [h0, h2, h32, h4, h44, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · linarith only [h0, h2, h4, h43, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                      · rcases m.htr 2 5 6 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                          · linarith only [h0, h2, h34, h4, h49, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · linarith only [h0, h2, h4, h49, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                          · linarith only [h0, h2, h34, h4, h52, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                          · linarith only [h0, h2, h4, h52, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b]
                · linarith only [h7, hc56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
            · linarith only [h5, hc35, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h4, hc34, hlam, hphi, ht12, ht23, u1ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht12, u1ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht12, u1ehi1]
    · linarith only [h1, hc15, hlam, hphi, u1ehi0]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n8l_sAA8_M_IR_M_LI (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
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
  have u1elo5 := h1elo (m.d 1 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 1 6 (by decide) (by decide) with h4 | h4
          · rcases h0emin with h5 | h5 | h5 | h5 | h5 | h5
            · linarith only [h5, hlam, ht01, u1elo0]
            · linarith only [h0, h5, hlam, ht01, u1elo0]
            · linarith only [h1, h5, hlam, ht01, u1elo0]
            · linarith only [h2, h5, hlam, ht01, u1elo0]
            · linarith only [h3, h5, hlam, ht01, u1elo0]
            · linarith only [h4, h5, hlam, ht01, u1elo0]
          · linarith only [h4, hlam, hphi, ht01, u0ehi0, u1elo5]
        · linarith only [h0, h3, hlam, hphi, ht01, u0ehi1, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi1, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n8l_sAA8_M_IR_M_LR (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi6 := h1ehi (m.d 0 1) (by simp)
  have u1ehi7 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi7, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo1]

theorem n8l_sAA8_M_LI_H_I (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h9, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h15 | h15
    · linarith only [h15, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h15, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h39, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h50 | h50
    · linarith only [h50, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h50, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h53 | h53
    · linarith only [h53, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h53, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h56 | h56
    · linarith only [h56, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h56, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h60 | h60
    · linarith only [h60, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h60, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h64 | h64
    · linarith only [h64, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h64, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · linarith only [h67, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h67, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · linarith only [h70, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h70, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h73 | h73
    · linarith only [h73, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h73, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_M_LI_H_L (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
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
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 5 6 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h1, h10, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h10, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                    · linarith only [h1, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h13, h15, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
              · rcases m.htr 0 5 6 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                    · linarith only [h1, h21, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h19, h21, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h24, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h1, h26, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h24, h26, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 0 5 6 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h31, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h1, h33, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h2, h35, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                      · linarith only [h0, h29, h31, h33, h35, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h38, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                    · linarith only [h29, h40, h5, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h2, h42, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                      · linarith only [h2, h29, h40, h42, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
              · rcases m.htr 0 5 6 (by decide) (by decide) with h45 | h45
                · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                  · linarith only [h0, h46, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                    · linarith only [h1, h48, h5, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h2, h29, h5, h50, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                      · rcases m.htr 1 5 6 (by decide) (by decide) with h52 | h52
                        · linarith only [h3, h52, hc56, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                        · linarith only [h3, h45, h52, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                  · linarith only [h0, h55, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                    · linarith only [h1, h5, h57, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h2, h29, h59, hc05, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                      · rcases m.htr 1 5 6 (by decide) (by decide) with h61 | h61
                        · linarith only [h29, h3, h45, h61, hc04, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                          · linarith only [h0, h1, h4, h5, h55, h63, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                          · linarith only [h0, h4, h55, h63, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h66 | h66
            · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
              · rcases m.htr 0 5 6 (by decide) (by decide) with h68 | h68
                · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                  · linarith only [h0, h69, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                    · linarith only [h1, h71, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h66, h69, h71, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h74, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h1, h76, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h66, h74, h76, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
              · rcases m.htr 0 5 6 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                  · linarith only [h0, h80, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                    · linarith only [h1, h82, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h66, h80, h82, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                  · linarith only [h0, h85, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                    · linarith only [h1, h87, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b, u1elo0]
                    · linarith only [h1, h66, h85, h87, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 5 6 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                  · linarith only [h0, h92, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h1, h66, h94, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h2, h96, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                      · linarith only [h2, h90, h92, h94, h96, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                  · linarith only [h0, h99, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                    · linarith only [h101, h66, h90, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h103, h2, hc45, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                      · linarith only [h101, h103, h2, h90, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
              · rcases m.htr 0 5 6 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                  · linarith only [h0, h107, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                    · linarith only [h1, h109, h4, h66, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h111, h2, h66, h90, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                      · rcases m.htr 1 5 6 (by decide) (by decide) with h113 | h113
                        · linarith only [h113, h3, hc56, hlam, hphi, ht01, ht0b, ht6b, u1elo0]
                        · linarith only [h106, h113, h3, hc15, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                  · linarith only [h0, h116, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                    · linarith only [h1, h118, h66, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h120, h2, h66, h90, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b, u1elo0]
                      · rcases m.htr 1 5 6 (by decide) (by decide) with h122 | h122
                        · linarith only [h106, h122, hc05, hlam, hphi, ht01, ht0b, ht56, ht6b, u1elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                              · linarith only [h1, h116, h124, h126, h66, h90, hc12, hc23, hlam, hphi]
                              · rcases m.htr 3 5 6 (by decide) (by decide) with h128 | h128
                                · linarith only [h1, h106, h116, h125, h128, h66, h90, hc12, hc23, hlam, hphi]
                                · rcases m.htr 4 5 6 (by decide) (by decide) with h130 | h130
                                  · linarith only [h1, h116, h126, h128, h130, h66, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h116, h126, h130, h66, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                            · linarith only [h1, h116, h124, h125, h66, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h134 | h134
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                              · linarith only [h1, h116, h124, h134, h135, h66, h90, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h116, h124, h135, hc12, hc45, hlam, hphi, ht23, ht34]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                              · rcases m.htr 3 5 6 (by decide) (by decide) with h139 | h139
                                · rcases m.htr 4 5 6 (by decide) (by decide) with h140 | h140
                                  · linarith only [h1, h106, h116, h138, h140, h66, h90, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h1, h116, h139, h140, h66, h90, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h116, h134, h139, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                              · linarith only [h116, h124, h138, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht56, ht6b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n8l_sAA8_M_LI_H_R (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo0, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n8l_sAA8_M_LI_M_IR (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 1 6) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_M_LI_M_LR (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo5 := h1elo (m.d 1 6) (by simp)
  have u1ehi6 := h1ehi (m.d 0 1) (by simp)
  have u1ehi11 := h1ehi (m.d 1 6) (by simp)
  rcases m.htr 0 1 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi11, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo5]

theorem n8l_sAA8_M_LR_H_I (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h9, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h15 | h15
    · linarith only [h15, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h15, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h39 | h39
    · linarith only [h39, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h39, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h50 | h50
    · linarith only [h50, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h50, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h53 | h53
    · linarith only [h53, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h53, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h56 | h56
    · linarith only [h56, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h56, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h60 | h60
    · linarith only [h60, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo0]
    · linarith only [h60, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h64 | h64
    · linarith only [h64, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h64, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · linarith only [h67, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h67, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h70 | h70
    · linarith only [h70, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h70, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h73 | h73
    · linarith only [h73, hc15, hlam, hphi, ht0b, ht56, ht6b, p0_1, u0elo0]
    · linarith only [h73, hc01, hc16, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_M_LR_H_L (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi6 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi6, u1elo0]

theorem n8l_sAA8_M_LR_H_R (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo0, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n8l_sAA8_M_LR_M_IR (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 1 6) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, p0_1, u0elo0, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sAA8_M_LR_M_LR (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb1 : CMSig2_8_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5) (m.d 1 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi6 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo2]

end R2N4
