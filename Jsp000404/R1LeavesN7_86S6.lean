import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_M_IR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases h0bigk with h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi3]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, hlam, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h4, hc02, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, hc01, hlam, hphi, p6_1, u0ehi3]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, hc01, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6_1, u2ehi1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h2, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, hphi, ht01, ht12, ht23, p6_1, u0ehi3, u3elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, hphi, ht01, ht12, ht23, p6_1, u0ehi4, u3elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h2, h5, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6_1, u2ehi3]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hc02, hlam, hphi, p6_1, u0ehi2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h3, hc01, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, hlam, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h4, hc03, hlam, hphi, p6_1, u0ehi1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h4, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h4, hlam, hphi, ht01, ht12, ht23, p6_1, u0ehi3, u3elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
            · linarith only [h5, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · linarith only [h2, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h36 | h36
      · rcases m.htr 0 2 4 (by decide) (by decide) with h37 | h37
        · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
          · linarith only [h0, h1, h36, h38, hlam, hphi, ht23, u2ehi2, u3elo0]
          · linarith only [h0, h1, h36, h38, hc15, hlam, hphi, ht01, ht23, u0ehi2, u2ehi2, u3elo4]
        · linarith only [h36, h37, hc24, hlam, hphi, u2ehi2]
      · linarith only [h36, hlam, hphi, ht23, u2ehi0, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h43 | h43
    · rcases m.htr 0 2 3 (by decide) (by decide) with h44 | h44
      · rcases m.htr 0 2 4 (by decide) (by decide) with h45 | h45
        · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
          · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
            · rcases h0bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h46, hc01, hlam, hphi, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p48_1, u0ehi3]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p48_1, u0ehi0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, h46, hc12, hlam, hphi, ht01, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p48_1, u0ehi3]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h43, hc03, hlam, hphi, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h44, hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, hphi, ht01, ht12, ht23, p48_1, u0ehi3, u3elo0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, hphi, ht01, ht12, ht23, p48_1, u0ehi4, u3elo0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h43, hc04, hlam, hphi, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h45, hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, h45, hc12, hlam, hphi, ht01, p48_1, u0ehi2]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h0, h45, hc12, hlam, hphi, ht01, p48_1, u0ehi4]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h43, hlam, p48_1]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h43, hc01, hlam, hphi, p48_1, u0ehi1]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h46, hlam, p48_0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [h46, hlam, hphi, ht01, ht12, ht23, p48_1, u0ehi3, u3elo0]
              · have p48_0 := h48c.1
                have p48_1 := h48c.2.1
                have p48_2 := h48c.2.2.1
                have p48_3 := h48c.2.2.2
                linarith only [hlam, p48_0]
            · linarith only [h47, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h46, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h44, h45, hc24, hlam, hphi, u2ehi2]
      · linarith only [h44, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h78 | h78
      · rcases m.htr 0 2 4 (by decide) (by decide) with h79 | h79
        · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
            · rcases h0bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h0, hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h43, h80, hlam, p82_1]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hc01, hlam, hphi, p82_1, u0ehi3]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h43, hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hc02, hlam, hphi, p82_1, u0ehi0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p82_1, u0ehi2]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h0, hc12, hlam, hphi, ht01, p82_1, u0ehi3]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h0, h43, hc12, hlam, hphi, ht01, p82_1, u0ehi0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hc03, hlam, hphi, p82_1, u0ehi0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h78, hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hlam, hphi, ht01, ht12, ht23, p82_1, u0ehi3, u3elo0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h43, hlam, hphi, ht01, ht12, ht23, p82_1, u0ehi0, u3elo0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hc04, hlam, hphi, p82_1, u0ehi0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h79, hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h0, h79, hc12, hlam, hphi, ht01, p82_1, u0ehi2]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h0, h43, h79, hc12, hlam, hphi, ht01, p82_1, u0ehi0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h80, hc03, hlam, hphi, p82_1, u0ehi0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h80, hlam, hphi, ht23, p82_1, u2ehi0, u3elo0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h80, hlam, p82_0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [h80, hlam, hphi, ht01, ht12, ht23, p82_1, u0ehi3, u3elo0]
              · have p82_0 := h82c.1
                have p82_1 := h82c.2.1
                have p82_2 := h82c.2.2.1
                have p82_3 := h82c.2.2.2
                linarith only [hlam, p82_0]
            · linarith only [h81, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h80, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h78, h79, hc24, hlam, hphi, u2ehi2]
      · linarith only [h78, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_M_LR_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
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
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h6, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h4, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h3, h6, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, h2, h6, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h14, h16, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases h2bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          rcases p18_3 (m.d 0 2) (by simp) with h20 | h20
                          · rcases p18_3 (m.d 1 2) (by simp) with h21 | h21
                            · linarith only [h0, h21, hlam]
                            · rcases p18_3 (m.d 2 3) (by simp) with h23 | h23
                              · linarith only [h2, h23, hlam]
                              · linarith only [h23, h6, hlam]
                          · linarith only [h0, h20, hlam]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h12, h15, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          rcases p18_3 (m.d 0 2) (by simp) with h28 | h28
                          · rcases p18_3 (m.d 1 2) (by simp) with h29 | h29
                            · linarith only [h0, h29, hlam]
                            · rcases p18_3 (m.d 2 3) (by simp) with h31 | h31
                              · linarith only [h2, h31, hlam]
                              · linarith only [h14, h31, hlam]
                          · linarith only [h28, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h12, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, hlam, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h6, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h12, h15, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p18_1, u3elo2]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h12, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h2, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h12, h2, hc15, hlam, hphi, ht0b, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h15, h16, h2, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18_1]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h14, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h14, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h14, h2, hc25, hlam, hphi, ht0b, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h3, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h15, hlam, p18_0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [h0, h15, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, p18_1, u0elo0]
                        · have p18_0 := h18c.1
                          have p18_1 := h18c.2.1
                          have p18_2 := h18c.2.2.1
                          have p18_3 := h18c.2.2.2
                          linarith only [hlam, p18_0]
                    · linarith only [h15, h5, hc23, hlam, hphi, u3elo0]
                  · linarith only [h14, h6, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h60 | h60
          · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
            · linarith only [h2, h3, h61, hlam]
            · linarith only [h61, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
          · linarith only [h60, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h67 | h67
    · rcases m.htr 0 2 3 (by decide) (by decide) with h68 | h68
      · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
        · rcases m.htr 0 3 4 (by decide) (by decide) with h70 | h70
          · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                      · linarith only [h67, h72, h74, h76, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases h2bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h75, h76, hc34, hlam, hphi, ht0b, ht45, ht5b, p78_1, u0elo1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 2) (by simp) with h82 | h82
                          · rcases p78_3 (m.d 1 2) (by simp) with h83 | h83
                            · rcases p78_3 (m.d 2 3) (by simp) with h84 | h84
                              · linarith only [h68, h84, hlam]
                              · linarith only [h74, h84, hlam]
                            · linarith only [h0, h67, h74, h83, hc13, hlam, hphi, u3elo2]
                          · linarith only [h82, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 2) (by simp) with h89 | h89
                          · rcases p78_3 (m.d 1 2) (by simp) with h90 | h90
                            · rcases p78_3 (m.d 2 3) (by simp) with h91 | h91
                              · linarith only [h68, h91, hlam]
                              · linarith only [h75, h91, hlam]
                            · linarith only [h73, h90, hlam]
                          · linarith only [h89, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p78_1, u0ehi6]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 2) (by simp) with h98 | h98
                          · linarith only [h0, h98, hlam]
                          · linarith only [h68, h98, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 2) (by simp) with h101 | h101
                          · linarith only [h0, h101, hlam]
                          · linarith only [h0, h101, h67, h72, h74, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 2) (by simp) with h104 | h104
                          · linarith only [h0, h104, hlam]
                          · linarith only [h104, h69, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h68, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h72, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h67, h72, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h67, h72, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, hc24, hlam, hphi, ht01, ht12, p78_1, u0ehi5]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h67, h72, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p78_1, u0elo0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h74, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h67, h72, h74, h75, h76, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h69, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h73, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h75, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h69, hc24, hlam, hphi, ht0b, ht45, ht5b, p78_1, u0elo1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                    · linarith only [h71, h75, hc23, hlam, hphi, u3elo0]
                  · linarith only [h70, h74, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h69, h73, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h72, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h70, h71, hlam, hphi, ht01, ht12, ht23, u0ehi8, u3elo4]
          · linarith only [h70, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h128 | h128
          · rcases m.htr 0 3 5 (by decide) (by decide) with h129 | h129
            · linarith only [h0, h129, h67, h69, hlam]
            · linarith only [h129, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
          · linarith only [h128, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · linarith only [h0, h67, h68, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo2]
    · linarith only [h67, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem r1l7_20_12_14_H_L_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h3, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h12, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
              · linarith only [h0, h14, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                · linarith only [h1, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h11, h12, h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
            · linarith only [h0, h19, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
              · linarith only [h1, h19, h21, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                · linarith only [h1, h11, h23, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h11, h25, h3, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h25, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
      · rcases m.htr 0 2 3 (by decide) (by decide) with h30 | h30
        · linarith only [h0, h1, h30, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
          · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
            · linarith only [h0, h30, h33, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h33, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h32, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h29, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h38 | h38
    · rcases m.htr 0 1 4 (by decide) (by decide) with h39 | h39
      · rcases m.htr 0 2 3 (by decide) (by decide) with h40 | h40
        · rcases m.htr 0 3 4 (by decide) (by decide) with h41 | h41
          · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
            · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                · linarith only [h38, h44, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h38, h41, h42, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · linarith only [h0, h43, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h38, h42, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
            · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
              · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                · linarith only [h38, h41, h51, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                  · linarith only [h38, h41, h49, h53, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h0, h38, h49, h55, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h0, h39, h50, h57, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                        · linarith only [h57, h59, hc24, hlam, hphi, u4elo3]
                        · linarith only [h38, h41, h49, h59, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h50, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h49, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h0, h38, h40, hlam]
      · linarith only [h38, h39, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h66 | h66
      · rcases m.htr 0 2 3 (by decide) (by decide) with h67 | h67
        · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
          · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
            · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                  · linarith only [h67, h72, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h67, h68, h72, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h38, h67, h68, h71, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h66, h70, hc14, hlam, hphi, u4elo2]
            · linarith only [h0, h66, h69, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h38, h66, h68, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h79 | h79
          · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
            · linarith only [h67, h80, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h66, h80, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h66, h67, h79, hc14, hlam, hphi, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h84 | h84
        · rcases m.htr 0 3 4 (by decide) (by decide) with h85 | h85
          · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
            · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
              · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                  · linarith only [h84, h89, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h85, h89, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h84, h85, h88, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h87, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h86, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
            · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
                · linarith only [h38, h85, h95, h97, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h38, h97, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h96, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h84, h95, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
          · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
            · linarith only [h103, h84, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h103, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
            · linarith only [h0, h106, h84, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h0, h106, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_14_H_L_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h2, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h1, h2, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h9, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · linarith only [h0, h2, h6, h9, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h12 | h12
            · linarith only [h1, h12, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
              · linarith only [h14, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h14, h16, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h1, h14, h16, h18, h2, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h12, h2, h20, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h1, h14, h16, h2, h22, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h1, h14, h16, h2, h24, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h16, h20, h24, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
      · linarith only [h27, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
        · linarith only [h29, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
            · linarith only [h32, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
              · linarith only [h34, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · linarith only [h0, h1, h29, h31, h32, h34, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
            · linarith only [h37, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h39 | h39
              · linarith only [h39, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · linarith only [h0, h41, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h1, h41, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h44 | h44
    · rcases m.htr 0 1 4 (by decide) (by decide) with h45 | h45
      · linarith only [h45, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h47 | h47
        · linarith only [h47, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
          · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
            · linarith only [h0, h44, h47, h50, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · linarith only [h52, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · linarith only [h47, h49, h52, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h55 | h55
            · linarith only [h44, h55, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
              · linarith only [h57, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h0, h49, h60, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h44, h59, h60, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h59, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
      · linarith only [h64, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h66 | h66
        · linarith only [h66, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
            · linarith only [h69, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
              · linarith only [h71, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · linarith only [h66, h68, h71, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
            · linarith only [h74, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
              · linarith only [h76, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h68, h79, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h79, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h78, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_14_M_IR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                    · linarith only [h2, h6, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                  · linarith only [h2, h8, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                  · linarith only [h13, h2, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h17, h18, h6, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h20, h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · rcases h0bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h17, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi2]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hc01, hlam, hphi, p22_1, u0ehi2]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hc01, hlam, hphi, p22_1, u0ehi3]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h6, hc01, hlam, hphi, p22_1, u0ehi3]
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
                          linarith only [h20, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi3]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, hphi, ht01, ht12, p22_1, u0ehi3, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h6, hlam, hphi, ht01, ht12, p22_1, u0ehi3, u2elo0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h1, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hc03, hlam, hphi, p22_1, u0ehi1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, p22_1, u0ehi3]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h1, h6, hc01, hlam, hphi, p22_1, u0ehi3]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h6, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h2, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h4, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h6, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h0, h17, hc05, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi2]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h3, hlam, p22_1]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h5, hlam, p22_0]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [h3, hc02, hlam, hphi, p22_1, u0ehi3]
                        · have p22_0 := h22c.1
                          have p22_1 := h22c.2.1
                          have p22_2 := h22c.2.2.1
                          have p22_3 := h22c.2.2.2
                          linarith only [hlam, p22_0]
                  · linarith only [h17, h2, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                  · linarith only [h16, h49, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                  · linarith only [h2, h49, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
              · linarith only [h4, h5, h52, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h52, h55, h56, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h52, h58, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · linarith only [h4, h5, h58, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h2, h55, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                  · linarith only [h54, h62, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                  · linarith only [h2, h62, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
            · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
              · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                    · linarith only [h68, h69, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                    · linarith only [h2, h66, h69, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                  · linarith only [h2, h68, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h67, h73, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                  · linarith only [h2, h73, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h65, h66, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
              · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                    · linarith only [h79, h80, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                    · linarith only [h2, h77, h80, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                  · linarith only [h2, h79, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                  · linarith only [h78, h84, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                  · linarith only [h2, h84, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h77, h88, h89, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h4, h77, h91, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h4, h91, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h2, h88, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                  · linarith only [h87, h95, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                  · linarith only [h2, h95, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h100 | h100
      · rcases m.htr 0 2 5 (by decide) (by decide) with h101 | h101
        · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
          · rcases m.htr 0 3 5 (by decide) (by decide) with h103 | h103
            · rcases m.htr 0 4 5 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                · linarith only [h1, h105, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
                · linarith only [h0, h1, h100, h104, h105, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                · linarith only [h0, h1, h108, hlam]
                · linarith only [h0, h1, h108, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h101, h103, hlam]
          · linarith only [h0, h1, h100, h102, hlam]
        · linarith only [h100, h101, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · linarith only [h100, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_14_M_IR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases h0bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc02, hlam, hphi, p9_1, u0ehi2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, p9_1, u0ehi3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9_1, u2ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h3, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, h3, hc01, hlam, hphi, p9_1, u0ehi3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, h3, hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h4, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc04, hlam, hphi, p9_1, u0ehi2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p9_1, u0ehi4, u4elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc05, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hc01, hlam, hphi, p9_1, u0ehi2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hc01, hlam, hphi, p9_1, u0ehi3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                  · linarith only [h6, h8, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                · linarith only [h5, h7, hc25, hlam, hphi, u2ehi2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
              · linarith only [h38, h5, hc23, hlam, hphi, u2ehi3]
              · linarith only [h38, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
          · linarith only [h4, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h42 | h42
          · linarith only [h3, h42, hc23, hlam, hphi, u2ehi3]
          · linarith only [h42, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h45 | h45
        · rcases m.htr 0 2 4 (by decide) (by decide) with h46 | h46
          · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
            · linarith only [h0, h2, h47, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h0, h2, h45, h47, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · linarith only [h46, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h51 | h51
          · linarith only [h45, h51, hc23, hlam, hphi, u2ehi3]
          · linarith only [h51, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h55 | h55
    · rcases m.htr 0 1 5 (by decide) (by decide) with h56 | h56
      · rcases m.htr 0 2 3 (by decide) (by decide) with h57 | h57
        · rcases m.htr 0 2 4 (by decide) (by decide) with h58 | h58
          · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
            · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
              · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                  · rcases h0bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, p63_1, u0ehi2]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, p63_1, u0ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h55, h61, h62, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p63_1, u2ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, p63_1, u0ehi2]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, p63_1, u0ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h55, h61, h62, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p63_1, u2ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h57, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h57, hc12, hlam, hphi, ht01, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h57, hc12, hlam, hphi, ht01, p63_1, u0ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h55, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h58, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc04, hlam, hphi, p63_1, u0ehi2]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h55, h61, h62, hc12, hlam, hphi, ht01, ht23, ht34, p63_1, u0ehi4, u2ehi4, u4elo0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h56, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc05, hlam, hphi, p63_1, u0ehi1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h56, hc12, hlam, hphi, ht01, p63_1, u0ehi2]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, h56, hc12, hlam, hphi, ht01, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                  · linarith only [h60, h62, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                · linarith only [h0, h61, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h56, h60, hc24, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h0, h56, h57, h59, hc02, hlam, hphi, u0ehi4]
          · linarith only [h58, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
          · linarith only [h57, h94, hc23, hlam, hphi, u2ehi3]
          · linarith only [h94, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h97 | h97
        · rcases m.htr 0 2 4 (by decide) (by decide) with h98 | h98
          · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                  · linarith only [h102, h55, h56, hlam]
                  · linarith only [h100, h102, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                · linarith only [h0, h100, h101, h55, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h100, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h99, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h97, h98, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h109 | h109
          · linarith only [h109, h97, hc23, hlam, hphi, u2ehi3]
          · linarith only [h109, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
    · linarith only [h55, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

theorem r1l7_20_12_14_M_IR_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases h0bigk with h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc02, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc01, hlam, hphi, p2_1, u0ehi3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc01, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2_1, u2ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc03, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc03, hlam, hphi, p2_1, u0ehi3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc03, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2_1, u2ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc04, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc04, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc04, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc05, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hc01, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hc01, hlam, hphi, p2_1, u0ehi3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
    · rcases h0bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc15, hlam, hphi, ht01, p28_1, u0ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc15, hlam, hphi, ht01, p28_1, u0ehi2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc15, hlam, hphi, ht01, p28_1, u0ehi3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hlam, p28_1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc02, hlam, hphi, p28_1, u0ehi2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, h1, hc15, hlam, hphi, ht01, p28_1, u0ehi3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, h1, hc15, hlam, hphi, ht01, p28_1, u0ehi4]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc03, hlam, hphi, p28_1, u0ehi0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc03, hlam, hphi, p28_1, u0ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc03, hlam, hphi, p28_1, u0ehi3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, h1, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc04, hlam, hphi, p28_1, u0ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc04, hlam, hphi, p28_1, u0ehi2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, h1, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc15, hlam, hphi, ht01, p28_1, u0ehi1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc15, hlam, hphi, ht01, p28_1, u0ehi2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc15, hlam, hphi, ht01, p28_1, u0ehi3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h54 | h54
    · rcases h0bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hlam, p55_1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc01, hlam, hphi, p55_1, u0ehi2]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p55_1, u0ehi3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p55_1, u0ehi0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p55_1, u0ehi2]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p55_1, u0ehi3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h54, hc03, hlam, hphi, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc03, hlam, hphi, p55_1, u0ehi1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc03, hlam, hphi, p55_1, u0ehi3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc03, hlam, hphi, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h54, hc04, hlam, hphi, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, h54, hc04, hlam, hphi, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc04, hlam, hphi, p55_1, u0ehi2]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc04, hlam, hphi, p55_1, u0ehi4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h54, hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, h54, hlam, p55_1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h54, hc01, hlam, hphi, p55_1, u0ehi2]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, h54, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p55_1, u4ehi0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
    · rcases h0bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hlam, p81_1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p81_1, u0ehi2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p81_1, u0ehi3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hlam, p81_1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p81_1, u0ehi2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p81_1, u0ehi3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, h54, hc12, hlam, hphi, ht01, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc03, hlam, hphi, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc03, hlam, hphi, p81_1, u0ehi1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc03, hlam, hphi, p81_1, u0ehi3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hc03, hlam, hphi, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc04, hlam, hphi, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc04, hlam, hphi, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc04, hlam, hphi, p81_1, u0ehi2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hc04, hlam, hphi, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc05, hlam, hphi, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, h54, hc15, hlam, hphi, ht01, p81_1, u0ehi0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hc15, hlam, hphi, ht01, p81_1, u0ehi2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hc15, hlam, hphi, ht01, p81_1, u0ehi3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]

theorem r1l7_20_12_14_M_LI_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                · linarith only [h0, h3, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h0, h3, h4, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
            · linarith only [h1, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                · linarith only [h0, h14, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                · linarith only [h0, h17, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
            · linarith only [h1, h12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h24, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h1, h26, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                  · linarith only [h21, h26, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
              · linarith only [h1, h21, h23, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
            · linarith only [h1, h22, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
            · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h3, h33, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h1, h21, h35, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h1, h21, h37, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h3, h37, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                · linarith only [h0, h3, h40, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h1, h21, h42, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h0, h21, h3, h44, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h3, h44, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h1, h31, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · linarith only [h1, h2, hc25, hlam, hphi, u2ehi3]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h50 | h50
    · linarith only [h0, h50, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h52 | h52
      · linarith only [h0, h52, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h54 | h54
        · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
          · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
            · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h54, h60, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                    · linarith only [h55, h60, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                  · linarith only [h50, h55, h59, hlam]
                · linarith only [h0, h58, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h50, h55, h56, h57, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
              · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                    · linarith only [h54, h69, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                    · linarith only [h55, h69, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                  · linarith only [h50, h55, h68, hlam]
                · linarith only [h0, h67, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h54, h55, h66, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
            · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
              · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h50, h55, h78, hc24, hlam, hphi, u2ehi0]
                  · linarith only [h50, h75, h76, h78, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h54, h55, h75, h76, h77, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h50, h75, h76, hc45, hlam, hphi, ht23, ht34, u2ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
              · linarith only [h50, h55, h75, h83, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                  · linarith only [h50, h55, h85, h86, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h50, h86, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · linarith only [h54, h85, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
          · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
            · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
              · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                · linarith only [h0, h54, h93, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h93, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h50, h90, h91, h92, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
              · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                · linarith only [h0, h54, h98, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h98, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h90, h97, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
            · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                · linarith only [h0, h104, h54, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h104, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h102, h103, h50, hc45, hlam, hphi, ht23, ht34, u2ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
              · linarith only [h102, h108, h50, h90, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h110, h54, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h110, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
