import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sBT4_H_I_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5emax := hb5.2.2
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, ht45, u4ehi4]
    · linarith only [h0, h1, hlam, ht45, u4ehi0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
      · linarith only [h0, h5, hlam, ht45, u4ehi4]
      · linarith only [h0, h5, hlam, ht45, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h0, h4, h8, hlam, ht45, u4ehi0]
      · linarith only [h0, h8, hlam, ht45, u4ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
    · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
        · linarith only [h0, h13, hlam, ht45, u4ehi4]
        · linarith only [h0, h13, hlam, ht45, u4ehi2]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
        · linarith only [h0, h12, h16, hlam, ht45, u4ehi1]
        · linarith only [h0, h16, hlam, ht45, u4ehi2]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
      · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
        · linarith only [h0, h11, h20, hlam, ht45, u4ehi0]
        · linarith only [h0, h20, hlam, ht45, u4ehi2]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
        · linarith only [h0, h11, h23, hlam, ht45, u4ehi0]
        · linarith only [h0, h23, hlam, ht45, u4ehi2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
    · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
      · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
          · linarith only [h0, h29, hlam, ht45, u4ehi4]
          · linarith only [h0, h29, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
          · linarith only [h0, h28, h32, hlam, ht45, u4ehi2]
          · linarith only [h0, h32, hlam, ht45, u4ehi3]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
        · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
          · linarith only [h0, h27, h36, hlam, ht45, u4ehi1]
          · linarith only [h0, h36, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
          · linarith only [h0, h35, h39, hlam, ht45, u4ehi2]
          · linarith only [h0, h39, hlam, ht45, u4ehi3]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
      · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
        · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
          · linarith only [h0, h26, h44, hlam, ht45, u4ehi0]
          · linarith only [h0, h44, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h43, h47, hlam, ht45, u4ehi2]
          · linarith only [h0, h47, hlam, ht45, u4ehi3]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
        · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
          · linarith only [h0, h26, h51, hlam, ht45, u4ehi0]
          · linarith only [h0, h51, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
          · linarith only [h0, h26, h54, hlam, ht45, u4ehi0]
          · linarith only [h0, h54, hlam, ht45, u4ehi3]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sBT4_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h4ehi := hb4.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sBT4_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h5ehi := hb5.1
  have h4elo := hb4.1
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h4, h6, h8, hlam]
              · linarith only [h3, h4, h8, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h15, h3, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h18, h19, h2, h21, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u4elo2, u5ehi4]
            · linarith only [h0, h18, h2, h21, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
          · linarith only [h18, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
            · linarith only [h1, h26, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h1, h18, h2, h26, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h31, h35, hc24, hlam, hphi, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h30, h34, h38, hc24, hlam, hphi, u4elo4]
        · linarith only [h0, h30, h33, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
      · linarith only [h30, h42, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
            · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h46, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h49, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h0, h44, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sBT4_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h4ehi := hb4.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht45, u4ehi3, u5elo0]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi2, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sBT4_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h5elo := hb5.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · linarith only [h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12 | h12
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h12, h14, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h16, h18, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h12, h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h12, h2, h21, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h12, h13, h2, h23, hc24, hc25, hlam, hphi, ht0b, ht5b, u0elo0, u4elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                · linarith only [h1, h23, h25, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h12, h13, h2, h25, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · linarith only [h12, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 2 3 (by decide) (by decide) with h31 | h31
      · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
        · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
              · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h31, h37, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h31, h33, h37, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h30, h32, h35, h36, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h0, h35, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h30, h31, h34, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                  · linarith only [h31, h46, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h30, h44, h46, h48, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h48, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h30, h32, h44, h45, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h0, h44, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h30, h31, h43, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
        · linarith only [h32, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
        · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
          · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
              · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h0, h30, h31, h57, h58, h60, h62, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h62, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h30, h31, h58, h60, h61, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h0, h30, h31, h58, h60, hc24, hlam, hphi, u4elo3]
                · linarith only [h31, h55, h57, h59, hlam]
              · linarith only [h0, h31, h57, h58, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
              · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                      · linarith only [h30, h69, h71, h73, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h73, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h57, h72, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h30, h57, h69, h71, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h30, h55, h69, h70, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h0, h30, h69, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h30, h31, h56, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h30, h55, hc14, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
        · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
            · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h82, h88, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h82, h84, h88, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h30, h83, h86, h87, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h86, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h82, h85, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
            · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
              · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h82, h97, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h82, h99, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h99, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h96, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h95, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h82, h94, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h83, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h106 | h106
        · rcases m.htr 0 3 4 (by decide) (by decide) with h107 | h107
          · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                      · linarith only [h107, h113, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h113, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h112, h82, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h106, h111, h82, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h106, h108, h110, h82, hlam]
              · linarith only [h106, h108, h109, h82, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                      · linarith only [h107, h124, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h124, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h108, h123, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h108, h120, h122, h30, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h106, h120, h121, h30, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h120, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
            · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
              · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                  · linarith only [h106, h107, h131, h134, h82, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h106, h134, h82, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h106, h133, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h106, h131, h132, h82, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
              · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                  · linarith only [h106, h107, h131, h139, h141, h82, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h131, h141, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h106, h107, h139, h140, h30, h82, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h139, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h106, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

theorem n7l_sBT4_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h4ehi := hb4.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sBT4_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h5ehi := hb5.2.1
  have h4elo := hb4.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
        · linarith only [h3, h5, hc04, hlam, hphi, u4elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
          · linarith only [h5, h7, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
            · linarith only [h0, h1, h3, h9, hlam]
            · linarith only [h0, h1, h9, hc34, hlam, hphi, u4elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
    · linarith only [h12, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
      · linarith only [h14, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
        · linarith only [h0, h14, h16, hc03, hlam, hphi, ht34, u4elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
          · linarith only [h0, h14, h18, hc03, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h14, h20, hc03, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h20, hc03, hlam, hphi, ht34, u4elo4]

theorem n7l_sBT4_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h4ehi := hb4.1
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sBT4_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h3, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h1, h10, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h12, h3, h8, hc04, hlam, hphi, u4elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h10, h16, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h12, h18, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h12, h20, hc14, hlam, hphi, u4elo3]
                          · linarith only [h20, h8, hc13, hlam, hphi, ht34, u4elo4]
            · linarith only [h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h5, h6, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
          · linarith only [h0, h1, h25, h5, hc24, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
            · linarith only [h0, h1, h27, h5, hlam, hphi, u5ehi7, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h1, h29, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                · linarith only [h0, h1, h31, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h3, h33, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h33, h37, hc14, hlam, hphi, u4elo2]
                        · linarith only [h25, h37, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h36, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h35, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
    · linarith only [h42, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
      · linarith only [h44, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
          · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                  · linarith only [h44, h51, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h42, h46, h54, hc01, hc12, hlam, hphi]
                      · linarith only [h50, h51, h53, h54, hc34, hlam, hphi, ht45, u5elo4]
                    · linarith only [h49, h51, h53, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h50, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h49, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h46, h48, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h46, h47, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
          · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
              · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h44, h66, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                      · linarith only [h0, h42, h46, h63, h69, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h46, h63, h65, h69, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · linarith only [h0, h46, h68, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h65, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h46, h63, h64, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi7]
            · linarith only [h62, h63, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
            · linarith only [h62, h76, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h44, h62, h80, hc04, hlam, hphi, u4elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                        · linarith only [h62, h80, h84, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h62, h84, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h46, h79, h83, hlam]
                    · linarith only [h0, h42, h46, h78, h79, h80, h82, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h78, h79, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h0, h78, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]

theorem n7l_sBT4_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h6 | h6
        · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h1, h6, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h9 | h9
      · rcases m.htr 0 1 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h10, h9, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h13 | h13
        · linarith only [h13, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h0, h13, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
    · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
      · rcases m.htr 0 1 5 (by decide) (by decide) with h18 | h18
        · linarith only [h18, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h17, h18, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h21 | h21
        · linarith only [h21, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h16, h21, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
      · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
        · linarith only [h25, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · linarith only [h24, h25, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
        · linarith only [h28, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h30 | h30
          · rcases m.htr 0 2 4 (by decide) (by decide) with h31 | h31
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
                · linarith only [h30, h33, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                · linarith only [h32, h33, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
                · linarith only [h36, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h31, h38, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                                · linarith only [h30, h32, h46, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                                  · linarith only [h30, h32, h36, h38, h45, h48, hlam, hphi, u5ehi5, u5elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                                    · linarith only [h31, h38, h50, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                                      · linarith only [h16, h32, h38, h40, h43, h52, hc01, hc12, hlam, hphi]
                                      · linarith only [h16, h32, h45, h52, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                              · linarith only [h24, h45, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h16, h44, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h16, h36, h43, h57, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h16, h57, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h42, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h31, h38, h41, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h30, h40, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
              · linarith only [h30, h31, h63, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                · linarith only [h30, h65, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                  · linarith only [h67, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
                  · linarith only [h30, h31, h67, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h70 | h70
            · rcases m.htr 0 3 4 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
                · linarith only [h72, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
                · linarith only [h30, h70, h72, hc24, hlam, hphi, ht45, u5elo3]
              · linarith only [h30, h70, h71, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                · linarith only [h77, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
                · linarith only [h76, h77, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
                · linarith only [h80, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi8]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h82, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                                · linarith only [h16, h76, h84, h90, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h30, h87, h90, hc01, hc13, hlam, hphi]
                              · linarith only [h24, h89, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h16, h88, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                            · linarith only [h0, h30, h80, h87, h95, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h16, h95, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h86, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h30, h84, h85, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                      · linarith only [h0, h100, h70, h84, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                                  · linarith only [h0, h100, h102, h106, h107, h30, h80, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h100, h102, h106, h107, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                                · linarith only [h0, h102, h105, h106, h30, h76, h82, h84, hc01, hc34, hlam, hphi, ht12, ht23, u5ehi7, u5elo1]
                              · linarith only [h105, h24, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h103, h104, h30, h76, hc02, hc35, hlam, hphi, ht23]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                            · linarith only [h103, h113, h30, h80, hc02, hc34, hlam, hphi, ht23]
                            · linarith only [h113, h16, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h102, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem n7l_sBT4_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h4ehi := hb4.1
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi9]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sBT4_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sBT4_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5emax := hb5.2.2
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · rcases h5emax with h6 | h6 | h6 | h6 | h6
              · linarith only [h6, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
              · linarith only [h3, h6, hlam, ht45, u4ehi4]
              · linarith only [h4, h6, hlam, ht45, u4ehi4]
              · linarith only [h5, h6, hlam, ht45, u4ehi4]
              · linarith only [h6, hlam, ht45, u4ehi4]
            · rcases h5emax with h12 | h12 | h12 | h12 | h12
              · linarith only [h12, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
              · linarith only [h12, h3, h5, hlam, ht45, u4ehi3]
              · linarith only [h12, h4, h5, hlam, ht45, u4ehi3]
              · linarith only [h12, h5, hlam, ht45, u4ehi3]
              · linarith only [h12, h5, hlam, ht45, u4ehi3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
            · linarith only [h0, h1, h18, h2, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases h5emax with h20 | h20 | h20 | h20 | h20
              · linarith only [h20, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
              · linarith only [h20, h3, h4, hlam, ht45, u4ehi2]
              · linarith only [h20, h4, hlam, ht45, u4ehi2]
              · linarith only [h18, h20, hlam, ht45, u4ehi3]
              · linarith only [h20, h4, hlam, ht45, u4ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
            · linarith only [h0, h1, h2, h27, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
            · rcases h5emax with h29 | h29 | h29 | h29 | h29
              · linarith only [h29, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
              · linarith only [h29, h3, hlam, ht45, u4ehi1]
              · linarith only [h26, h29, h3, hlam, ht45, u4ehi1]
              · linarith only [h27, h29, hlam, ht45, u4ehi3]
              · linarith only [h29, h3, hlam, ht45, u4ehi1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
            · linarith only [h0, h1, h2, h3, h35, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
            · rcases h5emax with h37 | h37 | h37 | h37 | h37
              · linarith only [h37, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
              · linarith only [h3, h37, hlam, ht45, u4ehi1]
              · linarith only [h26, h37, hlam, ht45, u4ehi2]
              · linarith only [h35, h37, hlam, ht45, u4ehi3]
              · linarith only [h3, h37, hlam, ht45, u4ehi1]
      · linarith only [h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT4_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sBT4_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h3, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h10, h12, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h10, h14, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h10, h12, h16, h3, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h1, h14, h18, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h2, h20, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h16, h20, h5, h6, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h2, h23, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h2, h25, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h1, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h2, h31, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h27, h33, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h27, h31, h33, h5, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h27, h30, h5, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h0, h2, h27, h37, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                        · linarith only [h0, h2, h37, h40, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h27, h39, h40, h5, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                        · linarith only [h39, h43, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                          · linarith only [h0, h2, h4, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h39, h45, h5, hc12, hc45, hlam, hphi, ht23, ht34]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc13, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sBT4_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sBT4_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
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
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4, u4elo0]
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

theorem n7l_sBT4_M_IR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]

theorem n7l_sBT4_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.2.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h5, h7, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h4, h8, hc24, hlam, hphi, u4elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h11, h4, hc24, hlam, hphi, u4elo0]
              · linarith only [h3, h5, h6, hc23, hlam, hphi, ht34, u4elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h15, h17, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h17, h4, hc24, hlam, hphi, u4elo0]
                · linarith only [h16, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h2, h21, h23, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h22, h23, hc34, hlam, hphi, u4elo2]
                  · linarith only [h22, h4, hc24, hlam, hphi, u4elo0]
                · linarith only [h21, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
        · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
            · linarith only [h2, h30, h31, h32, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
              · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h2, h30, h36, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h31, h36, hc24, hlam, hphi, u4elo0]
                · linarith only [h2, h35, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h2, h30, h34, hc12, hc23, hlam, hphi]
          · linarith only [h31, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
        · linarith only [h30, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
    · rcases m.htr 0 2 3 (by decide) (by decide) with h45 | h45
      · rcases m.htr 0 2 4 (by decide) (by decide) with h46 | h46
        · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
          · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                  · linarith only [h0, h44, h49, h51, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · linarith only [h47, h51, hc24, hlam, hphi, u4elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                  · linarith only [h0, h44, h49, h54, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · linarith only [h47, h54, hc24, hlam, hphi, u4elo0]
              · linarith only [h0, h49, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h44, h47, h48, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · linarith only [h47, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
        · linarith only [h0, h44, h46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h61 | h61
        · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
          · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
            · linarith only [h0, h44, h45, h62, h63, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h44, h62, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · linarith only [h62, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
        · linarith only [h0, h44, h61, hc14, hlam, hphi, u4elo2]
    · linarith only [h44, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

theorem n7l_sBT4_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
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
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, ht34, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4, u4elo0]
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

theorem n7l_sBT4_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo1]
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
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo2]
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
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo3]
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

theorem n7l_sBT4_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h5ehi := hb5.2.2.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h10, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · linarith only [h11, h5, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · linarith only [h14, h5, hc24, hlam, hphi, u4elo0]
                    · linarith only [h5, h9, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                      · linarith only [h19, h6, h8, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h0, h21, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · linarith only [h18, h21, hc24, hlam, hphi, u4elo1]
                    · linarith only [h18, h5, hc14, hlam, hphi, u4elo0]
                · linarith only [h4, h6, h7, hc23, hlam, hphi, ht34, u4elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h26, h28, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h28, h5, hc14, hlam, hphi, u4elo0]
                  · linarith only [h26, h27, h6, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                          · linarith only [h1, h32, h36, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · linarith only [h33, h36, hc34, hlam, hphi, u4elo1]
                        · linarith only [h26, h33, h35, hlam]
                      · linarith only [h34, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h33, h5, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                      · linarith only [h0, h3, h32, h42, h43, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                      · linarith only [h43, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h42, h5, hc14, hlam, hphi, u4elo0]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h49 | h49
          · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
              · linarith only [h3, h49, h50, h51, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                        · linarith only [h3, h49, h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                        · linarith only [h2, h55, h57, hc24, hlam, hphi, u4elo0]
                      · linarith only [h3, h56, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h50, h55, hc14, hlam, hphi, u4elo0]
                  · linarith only [h51, h53, h54, hc24, hlam, hphi, u4elo3]
                · linarith only [h3, h49, h53, hc12, hc23, hlam, hphi]
            · linarith only [h50, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h49, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h0, h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 2 3 (by decide) (by decide) with h68 | h68
        · linarith only [h0, h1, h68, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h70 | h70
          · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
              · linarith only [h68, h70, h71, h72, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h1, h74, h76, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h71, h75, h76, hc34, hlam, hphi, u4elo0]
                  · linarith only [h0, h1, h75, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h70, h72, h74, hc12, hc23, hlam, hphi]
            · linarith only [h71, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h70, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h0, h67, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h84 | h84
    · rcases m.htr 0 1 4 (by decide) (by decide) with h85 | h85
      · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
        · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
          · rcases m.htr 0 4 5 (by decide) (by decide) with h88 | h88
            · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
              · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                    · linarith only [h0, h84, h91, h92, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h88, h92, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                    · linarith only [h0, h85, h95, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h88, h95, hc14, hlam, hphi, u4elo0]
                · linarith only [h0, h90, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h85, h88, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · linarith only [h88, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h86, h87, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h84, h86, hlam]
      · linarith only [h84, h85, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h104 | h104
      · rcases m.htr 0 2 3 (by decide) (by decide) with h105 | h105
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
            · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
              · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h104, h108, h111, h84, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h107, h111, hc14, hlam, hphi, u4elo0]
                  · linarith only [h110, h84, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h0, h104, h107, h109, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi9]
              · linarith only [h0, h104, h105, h107, h108, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
            · linarith only [h107, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h106, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h119 | h119
          · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
              · linarith only [h0, h105, h121, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h104, h120, h121, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · linarith only [h120, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
          · linarith only [h119, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h104, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

theorem n7l_sBT4_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
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
    linarith only [hlam, hphi, ht45, p0_1, u4ehi0, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_M_LI_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5emax := hb5.2.2
  have h4ehi := hb4.1
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, ht45, u4ehi4]
    · linarith only [h0, h1, hlam, ht45, u4ehi0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
      · linarith only [h0, h5, hlam, ht45, u4ehi4]
      · linarith only [h4, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h0, h4, h8, hlam, ht45, u4ehi0]
      · linarith only [h0, h8, hlam, ht45, u4ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
    · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
        · linarith only [h0, h13, hlam, ht45, u4ehi4]
        · linarith only [h11, h13, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
      · linarith only [h11, h12, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
      · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
        · linarith only [h0, h11, h18, hlam, ht45, u4ehi0]
        · linarith only [h0, h18, hlam, ht45, u4ehi2]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h11, h21, hlam, ht45, u4ehi0]
        · linarith only [h0, h21, hlam, ht45, u4ehi2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
    · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
      · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
        · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
          · linarith only [h0, h27, hlam, ht45, u4ehi4]
          · linarith only [h24, h27, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
        · linarith only [h24, h26, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
      · linarith only [h24, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
      · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
        · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
          · linarith only [h0, h24, h34, hlam, ht45, u4ehi0]
          · linarith only [h0, h34, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
          · linarith only [h0, h24, h37, hlam, ht45, u4ehi0]
          · linarith only [h0, h37, hlam, ht45, u4ehi3]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
        · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
          · linarith only [h0, h24, h41, hlam, ht45, u4ehi0]
          · linarith only [h0, h41, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
          · linarith only [h0, h24, h44, hlam, ht45, u4ehi0]
          · linarith only [h0, h44, hlam, ht45, u4ehi3]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sBT4_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h4ehi := hb4.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sBT4_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5ehi := hb5.1
  have h4elo := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
            · linarith only [h3, h7, hc04, hlam, hphi, u4elo1]
            · linarith only [h0, h1, h6, h7, hc24, hlam, hphi, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h10, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h10, h14, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1, h14, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1, h17, hc24, hlam, hphi, u4elo4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h12, h20, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h1, h22, h3, hlam]
                  · linarith only [h0, h1, h12, h22, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h0, h1, h5, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h26 | h26
    · linarith only [h26, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
      · linarith only [h0, h28, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
            · linarith only [h0, h28, h32, hc02, hlam, hphi, ht23, ht34, u4elo1]
            · linarith only [h0, h30, h32, hc02, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h0, h30, h31, hc02, hc25, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
          · linarith only [h30, h36, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
              · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h38, h42, hc14, hlam, hphi, u4elo2]
                  · linarith only [h0, h42, hc02, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                  · linarith only [h45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
                  · linarith only [h0, h45, hc02, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                · linarith only [h40, h48, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h50, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
                  · linarith only [h0, h50, hc02, hlam, hphi, ht23, ht34, u4elo4]

theorem n7l_sBT4_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h4ehi := hb4.1
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
      · linarith only [h0, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
    · linarith only [h0, h1, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sBT4_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have h4elo := hb4.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
    · linarith only [h0, h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo4]

theorem n7l_sBT4_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h2, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h8, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, h2, h5, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h10, h12, h13, h15, h2, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h12, h15, h2, hc24, hc45, hlam, hphi]
                  · linarith only [h12, h4, h5, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
              · linarith only [h19, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h2, h21, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h2, h24, h5, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h21, h26, h7, hc14, hlam, hphi, ht01, u0ehi7]
                      · linarith only [h0, h2, h23, h26, hc24, hc45, hlam, hphi]
                  · linarith only [h23, h4, h5, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h30 | h30
          · linarith only [h1, h2, h30, h4, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
              · linarith only [h33, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                · linarith only [h32, h33, h35, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h37, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h1, h2, h30, h37, h39, hc15, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h1, h2, h35, h39, h41, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                          · linarith only [h1, h2, h37, h41, h44, hc12, hc24, hlam, hphi]
                          · linarith only [h4, h44, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · linarith only [h32, h33, h43, hc23, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
              · linarith only [h1, h32, h48, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
                · linarith only [h1, h2, h50, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h4, h52, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h2, h54, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h1, h2, h32, h50, h54, h56, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                        · linarith only [h32, h58, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h1, h2, h52, h56, h60, hc12, hc24, hlam, hphi]
                          · linarith only [h4, h60, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h63 | h63
      · linarith only [h63, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h65 | h65
        · linarith only [h0, h1, h65, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h67 | h67
          · linarith only [h0, h67, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
            · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
              · linarith only [h70, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
                · linarith only [h69, h70, h72, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h1, h65, h69, h70, h74, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h1, h67, h69, h70, h76, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                      · linarith only [h0, h1, h72, h74, h78, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h1, h78, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h81 | h81
              · linarith only [h81, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
                · linarith only [h83, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                  · linarith only [h0, h1, h83, h85, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                    · linarith only [h0, h1, h83, h87, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h1, h83, h85, h89, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h1, h89, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h92 | h92
    · rcases m.htr 0 1 5 (by decide) (by decide) with h93 | h93
      · linarith only [h93, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h95 | h95
        · rcases m.htr 0 2 5 (by decide) (by decide) with h96 | h96
          · linarith only [h96, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
            · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
              · linarith only [h99, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h101, h92, h96, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                    · linarith only [h0, h104, h96, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h104, h92, hc25, hlam, hphi, ht01, ht12, u0ehi8]
                  · linarith only [h0, h103, h92, hc24, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h108 | h108
              · linarith only [h108, h92, h98, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h110, h92, h96, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h0, h113, h96, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h113, h92, h98, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h0, h112, h92, h98, hc24, hlam, hphi, ht01, ht12, u0ehi7]
        · linarith only [h0, h92, h95, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h118 | h118
      · linarith only [h118, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
        · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
          · linarith only [h121, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
            · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h124, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                · linarith only [h123, h124, h126, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h121, h129, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h129, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h120, h128, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
              · linarith only [h133, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                · linarith only [h120, h121, h135, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                    · linarith only [h121, h138, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h138, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h120, h137, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h142 | h142
          · linarith only [h142, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h144 | h144
            · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
              · linarith only [h145, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
                · linarith only [h144, h145, h147, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                  · linarith only [h120, h149, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h149, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h152 | h152
              · linarith only [h152, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                · linarith only [h154, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                  · linarith only [h0, h120, h156, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h156, hc24, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sBT4_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h5ehi := hb5.1
  have h4ehi := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h3, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
        · linarith only [h2, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
              · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                · linarith only [h11, h3, h7, h8, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h2, h5, hlam, hphi, u0ehi8, u0elo2]
                  · linarith only [h10, h11, h13, h7, h8, hc45, hlam, hphi, u4ehi3]
              · linarith only [h10, h2, h3, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
            · linarith only [h17, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                · linarith only [h2, h20, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h2, h22, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                  · linarith only [h19, h20, h22, h7, hc45, hlam, hphi, u4ehi3]
              · linarith only [h19, h2, h3, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
      · linarith only [h26, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
        · linarith only [h28, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
          · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
            · linarith only [h0, h31, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
              · linarith only [h2, h33, hc13, hlam, hphi, ht01, u0ehi7]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                · linarith only [h26, h30, h35, hc12, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                  · linarith only [h28, h37, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h2, h37, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
            · linarith only [h30, h40, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
              · linarith only [h2, h42, hc13, hlam, hphi, ht01, u0ehi7]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                · linarith only [h26, h44, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                  · linarith only [h2, h28, h46, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                  · linarith only [h2, h46, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]

theorem n7l_sBT4_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
      · linarith only [h1, h2, hc14, hlam, hphi, u4elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo1]

theorem n7l_sBT4_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h4ehi := hb4.1
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
    · linarith only [h8, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
    · linarith only [h8, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h11 | h11
    · linarith only [h11, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h11, hc15, hlam, hphi, ht01, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
    · linarith only [h14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo4, u4ehi4]
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
    · linarith only [h18, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
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
    · linarith only [h22, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h22, hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h25 | h25
    · linarith only [h25, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
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
    · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h29, hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h32 | h32
    · linarith only [h32, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
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
    · linarith only [h36, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi4]
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
    · linarith only [h40, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi1]
    · linarith only [h40, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h43 | h43
    · linarith only [h43, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi2]
    · linarith only [h43, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 5) (by simp) with h46 | h46
    · linarith only [h46, hlam, hphi, ht0b, ht5b, p0_1, u0elo4, u5ehi3]
    · linarith only [h46, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi9, u4elo4]
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

theorem n7l_sBT4_M_LR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem n7l_sBT4_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h5emax := hb5.2.2.1
  have h4ehi := hb4.1
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi9]
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi3, u5elo1]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi2, u5elo1]
  · linarith only [h0, hlam, hphi, ht45, u4ehi1, u5elo4]

theorem n7l_sBT4_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h5ehi := hb5.2.2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
        · linarith only [h1, h2, h3, hc34, hlam, hphi, u4elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
        · linarith only [h1, h6, hc14, hlam, hphi, u4elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo1]

theorem n7l_sBT4_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h4bigk := hb4.1
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h7, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h10, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h14, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h17, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h26, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h29, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h35, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h38, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h38, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h47, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h52, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h58, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h55, h63, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h63, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h70 | h70
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · linarith only [h72, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h74 | h74
          · rcases p0_3 (m.d 4 5) (by simp) with h75 | h75
            · linarith only [h75, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h70, h75, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h78 | h78
            · linarith only [h78, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h70, h78, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
      · linarith only [h71, hlam, p0_0]
    · linarith only [h70, hc14, hlam, hphi, ht01, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h88 | h88
            · linarith only [h88, hc34, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h83, h88, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h85, h93, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h83, h93, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
      · linarith only [h84, hlam, p0_0]
    · linarith only [h83, hc14, hlam, hphi, ht01, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h98 | h98
    · linarith only [h98, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
    · linarith only [h98, hc14, hlam, hphi, ht01, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h102 | h102
    · rcases p0_3 (m.d 1 4) (by simp) with h103 | h103
      · linarith only [h103, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h105 | h105
        · rcases p0_3 (m.d 3 4) (by simp) with h106 | h106
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h102, h107, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h110 | h110
            · linarith only [h110, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h102, h110, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · linarith only [h105, hlam, p0_0]
    · linarith only [h102, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
    · rcases p0_3 (m.d 1 4) (by simp) with h117 | h117
      · rcases p0_3 (m.d 2 4) (by simp) with h118 | h118
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h121, hc34, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h116, h121, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · linarith only [h118, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h125 | h125
        · rcases p0_3 (m.d 3 4) (by simp) with h126 | h126
          · linarith only [h126, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h128 | h128
            · linarith only [h117, h128, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h116, h128, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
        · linarith only [h125, hlam, p0_0]
    · linarith only [h116, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · linarith only [h133, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
    · linarith only [h133, hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h137 | h137
    · rcases p0_3 (m.d 1 4) (by simp) with h138 | h138
      · linarith only [h138, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h140 | h140
        · rcases p0_3 (m.d 3 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h137, h142, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · linarith only [h141, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h146 | h146
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h137, h147, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · linarith only [h146, hlam, p0_0]
    · linarith only [h137, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
    · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
      · rcases p0_3 (m.d 2 4) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 4 5) (by simp) with h157 | h157
            · linarith only [h157, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h152, h157, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h161 | h161
        · linarith only [h161, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h153, h164, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h152, h164, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
          · linarith only [h163, hlam, p0_0]
    · linarith only [h152, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h170 | h170
    · linarith only [h170, hlam, hphi, ht0b, ht5b, p0_1, u0elo3, u5ehi9]
    · linarith only [h170, hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi8]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi8, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sBT4_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
              · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                · linarith only [h0, h1, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                · linarith only [h3, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h8, hlam, hphi, ht45, u4ehi2, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h1, h13, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
              · linarith only [h13, hlam, hphi, ht45, u4ehi2, u5elo4]
      · linarith only [h1, h2, hlam, hphi, ht45, u4ehi0, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
      · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
        · linarith only [h1, h17, h18, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
          · linarith only [h0, h20, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
          · linarith only [h1, h17, h20, hc13, hc34, hlam, hphi]
      · linarith only [h17, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
      · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                · linarith only [h24, h30, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                · linarith only [h30, hlam, hphi, ht45, u4ehi3, u5elo4]
              · linarith only [h29, hlam, hphi, ht45, u4ehi2, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
              · linarith only [h24, h28, h34, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
              · linarith only [h34, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h0, h25, h27, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
        · linarith only [h0, h24, h26, hlam, hphi, u0ehi5, u0elo2]
      · linarith only [h24, h25, hlam, hphi, ht45, u4ehi3, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
      · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
        · linarith only [h0, h24, h41, hc13, hlam, hphi, ht01, u0ehi5]
        · linarith only [h0, h41, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
      · linarith only [h0, h40, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo3]

end R2N4
