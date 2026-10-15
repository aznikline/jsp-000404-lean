import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_R_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · rcases h5bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc15, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc25, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc45, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc05, hlam, hphi, p7_1, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc45, hlam, hphi, p7_1, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc45, hlam, hphi, p7_1, u5elo3]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc05, hlam, hphi, p7_1, u5elo4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h3, h5, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, h6, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
              · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h5, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
          · linarith only [h2, h4, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · linarith only [h0, h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h39 | h39
    · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
      · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
        · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
          · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
              · rcases h5bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc15, hlam, hphi, p45_1, u5elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h43, hlam, hphi, ht34, ht45, p45_1, u3ehi4, u5elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, hphi, ht34, ht45, p45_1, u3ehi4, u5elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc45, hlam, hphi, p45_1, u5elo0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc05, hlam, hphi, p45_1, u5elo1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h43, hlam, hphi, ht34, ht45, p45_1, u3ehi4, u5elo1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, hphi, ht34, ht45, p45_1, u3ehi4, u5elo1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc45, hlam, hphi, p45_1, u5elo1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h39, hlam, p45_1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h41, hlam, p45_1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h39, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p45_1, u3ehi4]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc45, hlam, hphi, p45_1, u5elo2]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h40, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h42, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h43, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hc45, hlam, hphi, p45_1, u5elo3]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h39, h43, hc45, hlam, hphi, ht34, p45_1, u3ehi4]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h40, h44, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p45_1, u1ehi4]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h43, h44, hlam, p45_1]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [h44, hlam, p45_0]
                · have p45_0 := h45c.1
                  have p45_1 := h45c.2.1
                  have p45_2 := h45c.2.2.1
                  have p45_3 := h45c.2.2.2
                  linarith only [hlam, p45_0]
              · linarith only [h44, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h43, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
          · linarith only [h40, h42, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
        · linarith only [h41, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
      · linarith only [h40, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · linarith only [h0, h39, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo2]

theorem r1l7_11_13_25_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h3, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h6, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h12, h3, h6, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h12, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
            · linarith only [h4, h5, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
              · linarith only [h17, h3, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                · linarith only [h17, h19, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h19, h3, h4, hc34, hlam, hphi, u3ehi2]
            · linarith only [h16, h3, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
            · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
              · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h23, h26, h28, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h28, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h23, h26, h27, h3, hc35, hlam, hphi, u3ehi3]
                · linarith only [h24, h26, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h23, h25, h3, hlam]
            · linarith only [h23, h24, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
            · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
              · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h1, h36, h39, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h39, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h23, h35, h37, h38, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h3, h35, h37, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                · linarith only [h3, h35, h36, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                · linarith only [h3, h35, h44, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
            · linarith only [h35, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
    · linarith only [h0, h50, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h52 | h52
      · linarith only [h0, h52, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
        · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
          · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
            · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
              · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h54, h58, h60, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h60, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                  · linarith only [h59, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                  · linarith only [h58, h64, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h64, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
              · linarith only [h50, h57, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h56, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
          · linarith only [h50, h54, h55, hc24, hlam, hphi, ht12, u1ehi0]
        · linarith only [h0, h54, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_14_25_L_0_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
              · linarith only [h2, h4, h5, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h3, h5, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h12, h2, h3, h5, h7, h9, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h12, h14, h4, hc24, hlam, hphi, u4elo1]
                      · linarith only [h14, h4, h5, hc34, hlam, hphi, u4elo4]
                · linarith only [h4, h5, h9, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
            · linarith only [h18, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
              · linarith only [h1, h20, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                · linarith only [h20, h22, h3, h4, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h18, h24, h3, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h20, h26, h4, hc13, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h26, h28, hc24, hlam, hphi, u4elo3]
                      · linarith only [h28, h3, h4, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
            · linarith only [h0, h32, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
              · linarith only [h1, h34, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h34, h38, hc14, hlam, hphi, u4elo2]
                    · linarith only [h31, h32, h37, h38, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h31, h34, h41, hc34, hlam, hphi, u4elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                      · linarith only [h31, h41, h43, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h31, h32, h43, hc34, hlam, hphi, u4elo4]
                · linarith only [h3, h31, h36, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
            · linarith only [h31, h47, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
              · linarith only [h1, h49, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                    · linarith only [h31, h49, h53, hc13, hlam, hphi, ht34, u4elo2]
                    · linarith only [h3, h31, h51, h53, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h3, h31, h51, h52, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h3, h51, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
        · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
          · linarith only [h0, h2, h59, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
            · linarith only [h1, h2, h59, h61, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
              · linarith only [h1, h2, h63, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · linarith only [h1, h2, h58, h59, h63, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
          · linarith only [h0, h2, h66, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
            · linarith only [h1, h2, h66, h68, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
              · linarith only [h1, h2, h70, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · linarith only [h1, h2, h58, h66, h70, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h1, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h74 | h74
    · rcases m.htr 0 1 5 (by decide) (by decide) with h75 | h75
      · linarith only [h0, h75, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
        · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
          · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
            · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
              · linarith only [h74, h75, h77, h79, h80, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · linarith only [h74, h75, h80, hc14, hlam, hphi, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
              · linarith only [h0, h74, h83, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
              · linarith only [h74, h75, h83, hc14, hlam, hphi, u4elo4]
          · linarith only [h0, h74, h78, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
          · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
              · linarith only [h74, h75, h88, h89, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
              · linarith only [h74, h75, h89, hc14, hlam, hphi, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
              · linarith only [h0, h74, h88, h92, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · linarith only [h0, h74, h87, h88, h92, hc34, hlam, hphi, u4elo4]
          · linarith only [h0, h87, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
      · linarith only [h0, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
          · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
            · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h98, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                  · linarith only [h100, h102, h103, h98, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                  · linarith only [h102, h106, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h102, h108, h98, h99, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · linarith only [h101, h108, hc24, hlam, hphi, u4elo1]
              · linarith only [h101, h74, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
              · linarith only [h100, h112, h99, hlam]
              · linarith only [h112, h74, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · linarith only [h0, h99, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
          · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
            · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
              · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h116, h122, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                      · linarith only [h118, h122, hc34, hlam, hphi, u4elo1]
                    · linarith only [h118, h121, hc24, hlam, hphi, u4elo1]
                  · linarith only [h117, h120, h98, hlam]
                · linarith only [h117, h119, h98, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
              · linarith only [h118, h74, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
              · linarith only [h116, h117, h129, hlam]
              · linarith only [h129, h74, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · linarith only [h0, h116, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]

theorem r1l7_11_14_25_L_R_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · rcases h5bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc15, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc25, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc35, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht45, p7_1, u4ehi4, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, h6, hlam, hphi, ht45, p7_1, u4ehi4, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, h6, hlam, hphi, ht45, p7_1, u4ehi4, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hlam, hphi, ht45, p7_1, u4ehi4, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hc25, hlam, hphi, ht12, p7_1, u1ehi4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p7_1, u1ehi4, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hlam, hphi, ht45, p7_1, u4ehi4, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht45, p7_1, u4ehi4, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht45, p7_1, u4ehi4, u5elo3]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc05, hlam, hphi, p7_1, u5elo4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, h6, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
              · linarith only [h6, hlam, hphi, ht45, u4ehi3, u5elo4]
            · linarith only [h5, hlam, hphi, ht45, u4ehi2, u5elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
            · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
              · rcases h5bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hc15, hlam, hphi, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h35, hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h35, h4, hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h35, hlam, hphi, ht45, p37_1, u4ehi4, u5elo1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, h35, h4, hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, hc25, hlam, hphi, ht12, p37_1, u1ehi4]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h3, h4, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h4, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, h3, h4, hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h2, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h3, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, h3, hc25, hlam, hphi, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, h3, hlam, hphi, ht45, p37_1, u4ehi4, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, h36, hc34, hlam, hphi, ht12, ht23, p37_1, u1ehi4]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h0, h3, h35, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p37_1, u1ehi4]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h35, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h36, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
              · linarith only [h1, h3, h35, h36, h4, hlam, hphi, ht45, u4ehi3, u5elo0]
            · linarith only [h35, hlam, hphi, ht45, u4ehi2, u5elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
      · linarith only [h0, h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
    · linarith only [h0, h68, hc13, hlam, hphi, u1ehi4]
    · linarith only [h68, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_25_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · rcases h5bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc15, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc25, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc35, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc45, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc25, hlam, hphi, p9_1, u5elo1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, h8, hc45, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hc25, hlam, hphi, ht12, p9_1, u1ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p9_1, u1ehi4, u5elo2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h8, hc45, hlam, hphi, p9_1, u5elo2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc45, hlam, hphi, p9_1, u5elo2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h3, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h6, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc25, hlam, hphi, p9_1, u5elo3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc45, hlam, hphi, p9_1, u5elo3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h4, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h7, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc25, hlam, hphi, p9_1, u5elo4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h8, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                  · rcases h5bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p35_1, u1ehi4, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc25, hlam, hphi, p35_1, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc35, hlam, hphi, p35_1, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h8, hc34, hlam, hphi, ht45, p35_1, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h2, hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc25, hlam, hphi, p35_1, u5elo1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h2, h8, hc34, hlam, hphi, ht45, p35_1, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h2, h8, hc34, hlam, hphi, ht45, p35_1, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h2, hc25, hlam, hphi, ht12, p35_1, u1ehi4]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p35_1, u1ehi4, u5elo2]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h8, hc34, hlam, hphi, ht45, p35_1, u5elo2]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h8, hc34, hlam, hphi, ht45, p35_1, u5elo2]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h3, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h6, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc25, hlam, hphi, p35_1, u5elo3]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h8, hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h4, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h7, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc25, hlam, hphi, p35_1, u5elo4]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc35, hlam, hphi, p35_1, u5elo4]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                · linarith only [h4, h7, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo0]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
              · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                  · rcases h5bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p66_1, u1ehi4, u5elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc25, hlam, hphi, p66_1, u5elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc35, hlam, hphi, p66_1, u5elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc45, hlam, hphi, p66_1, u5elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h2, hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc25, hlam, hphi, p66_1, u5elo1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h2, h65, hc45, hlam, hphi, p66_1, u5elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h2, hc45, hlam, hphi, p66_1, u5elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h2, hc25, hlam, hphi, ht12, p66_1, u1ehi4]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p66_1, u1ehi4, u5elo2]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h65, hc45, hlam, hphi, p66_1, u5elo2]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc45, hlam, hphi, p66_1, u5elo2]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h3, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h63, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc25, hlam, hphi, p66_1, u5elo3]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc45, hlam, hphi, p66_1, u5elo3]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h4, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h64, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc25, hlam, hphi, p66_1, u5elo4]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h65, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                  · linarith only [h5, h63, h64, h65, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h4, h64, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo0]
              · linarith only [h63, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
        · linarith only [h0, h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h99 | h99
    · linarith only [h0, h99, hc13, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h101 | h101
      · linarith only [h0, h101, hc13, hlam, hphi, u1ehi4]
      · linarith only [h101, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_12_13_25_L_0_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                  · linarith only [h3, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h12, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
            · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
        · linarith only [h0, h3, hc12, hlam, hphi, u2elo0]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
      · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
        · linarith only [h0, h22, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
          · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
            · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                  · linarith only [h22, h24, h28, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h22, h24, h26, h28, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h21, h27, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
              · linarith only [h22, h24, h26, hlam]
            · linarith only [h0, h20, h25, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
            · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
              · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h0, h20, h38, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · linarith only [h24, h34, h36, h37, h38, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h21, h37, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h20, h21, h36, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
                · linarith only [h35, h43, hc34, hlam, hphi, u3ehi4]
                · linarith only [h43, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
            · linarith only [h0, h20, h34, hc12, hlam, hphi, u2elo2]
      · linarith only [h21, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
      · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
        · linarith only [h0, h49, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
          · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
            · linarith only [h20, h49, h52, hc02, hlam, hphi, u2elo2]
            · linarith only [h51, h52, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
            · linarith only [h20, h51, h55, hc02, hlam, hphi, u2elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
              · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                        · rcases h5bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hc15, hlam, hphi, p63_1, u5elo0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h20, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h20, hlam, hphi, ht34, ht45, p63_1, u3ehi4, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h20, hc45, hlam, hphi, p63_1, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hc05, hlam, hphi, p63_1, u5elo1]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h55, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h55, hlam, hphi, ht34, ht45, p63_1, u3ehi4, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h55, hc45, hlam, hphi, p63_1, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h48, hlam, hphi, ht34, ht45, p63_1, u3ehi4, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hc15, hlam, hphi, p63_1, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, hphi, ht34, ht45, p63_1, u3ehi4, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hc45, hlam, hphi, p63_1, u5elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h48, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h58, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h60, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h49, h57, h62, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p63_1, u2elo2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h48, hc45, hlam, hphi, ht34, p63_1, u3ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h49, h57, h58, h62, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p63_1, u2elo2, u3ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h61, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h62, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                        · linarith only [h62, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h51, h61, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h48, h60, hlam]
                  · linarith only [h0, h48, h59, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h48, h58, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                · linarith only [h57, h94, hc34, hlam, hphi, u3ehi4]
                · linarith only [h48, h94, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
      · linarith only [h48, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_12_14_25_L_0_L_0_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h1, h12, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                  · linarith only [h12, h5, hc24, hlam, hphi, u4elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                · linarith only [h0, h15, h16, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h15, h3, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h3, h4, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
          · linarith only [h21, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
            · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
              · linarith only [h23, h24, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                · linarith only [h21, h24, h26, hc13, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h1, h28, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                  · linarith only [h23, h28, h3, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
              · linarith only [h0, h3, h31, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h21, h33, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h1, h23, h35, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h23, h3, h37, hc13, hlam, hphi, ht34, u4elo3]
                    · linarith only [h0, h3, h37, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h0, h2, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
    · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
      · linarith only [h0, h43, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
      · linarith only [h42, h43, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
      · linarith only [h42, h46, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
        · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
          · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h48, h54, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                    · linarith only [h42, h50, h54, hc34, hlam, hphi, u4elo2]
                  · linarith only [h42, h50, h53, hlam]
                · linarith only [h0, h42, h50, h52, hc12, hlam, hphi, ht23, ht34, u4elo2, u5ehi9, u5elo3]
              · linarith only [h0, h48, h50, h51, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
              · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h50, h62, hc14, hlam, hphi, u4elo2]
                  · linarith only [h42, h62, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h49, h61, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
              · linarith only [h0, h48, h49, h60, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi8]
          · linarith only [h48, h49, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
          · linarith only [h48, h68, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
            · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
              · linarith only [h0, h48, h71, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h71, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
              · linarith only [h0, h48, h74, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h74, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem r1l7_12_14_25_L_0_L_R_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
            · linarith only [h0, h1, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
            · linarith only [h0, h1, h8, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
        · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
      · linarith only [h0, h2, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
        · linarith only [h1, h13, h14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
          · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h1, h17, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h1, h16, h19, hlam]
              · rcases h5emax with h21 | h21 | h21 | h21 | h21
                · linarith only [h0, h1, h16, h21, hlam, ht45, u4ehi3]
                · linarith only [h14, h21, hlam, ht45, u4ehi1]
                · linarith only [h16, h17, h21, hlam, ht45, u4ehi3]
                · linarith only [h19, h21, hlam, ht45, u4ehi3]
                · linarith only [h0, h1, h16, h21, hlam, ht45, u4ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
            · linarith only [h0, h1, h27, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
              · rcases h5emax with h30 | h30 | h30 | h30 | h30
                · linarith only [h1, h30, hlam, ht45, u4ehi0]
                · linarith only [h14, h30, hlam, ht45, u4ehi1]
                · linarith only [h27, h30, hlam, ht45, u4ehi2]
                · linarith only [h0, h1, h29, h30, hlam, ht45, u4ehi2]
                · linarith only [h0, h1, h30, hlam, ht45, u4ehi2]
              · rcases h5emax with h36 | h36 | h36 | h36 | h36
                · linarith only [h0, h1, h36, hlam, ht45, u4ehi2]
                · linarith only [h13, h14, h36, hlam, ht45, u4ehi2]
                · linarith only [h27, h36, hlam, ht45, u4ehi2]
                · linarith only [h29, h36, hlam, ht45, u4ehi3]
                · linarith only [h36, hlam, ht45, u4ehi4]
      · linarith only [h0, h13, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
    · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
      · linarith only [h0, h44, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
        · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
          · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
              · linarith only [h47, h49, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
              · linarith only [h0, h43, h49, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
            · linarith only [h0, h43, h48, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
            · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
              · rcases h5emax with h55 | h55 | h55 | h55 | h55
                · linarith only [h43, h55, hlam, ht45, u4ehi4]
                · linarith only [h46, h55, hlam, ht45, u4ehi4]
                · linarith only [h53, h55, hlam, ht45, u4ehi4]
                · linarith only [h54, h55, hlam, ht45, u4ehi4]
                · linarith only [h55, hlam, ht45, u4ehi4]
              · linarith only [h0, h43, h47, h54, hlam]
            · linarith only [h0, h43, h53, hlam]
        · linarith only [h0, h43, h46, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
      · linarith only [h0, h64, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
        · linarith only [h43, h64, h66, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
          · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
            · linarith only [h43, h68, h69, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
              · linarith only [h0, h68, h69, h71, hc02, hlam, hphi, u2elo2]
              · rcases h5emax with h73 | h73 | h73 | h73 | h73
                · linarith only [h43, h73, hlam, ht45, u4ehi0]
                · linarith only [h66, h73, hlam, ht45, u4ehi1]
                · linarith only [h0, h69, h73, hc02, hlam, ht23, ht34, ht45]
                · linarith only [h71, h73, hlam, ht45, u4ehi3]
                · linarith only [h0, h69, h73, hc02, hlam, ht23, ht34, ht45]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
            · linarith only [h43, h79, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
              · linarith only [h0, h79, h81, hc02, hc34, hlam, hphi, ht23]
              · rcases h5emax with h83 | h83 | h83 | h83 | h83
                · linarith only [h43, h83, hlam, ht45, u4ehi0]
                · linarith only [h66, h83, hlam, ht45, u4ehi1]
                · linarith only [h0, h79, h83, hc02, hlam, ht23, ht34, ht45]
                · linarith only [h0, h68, h81, h83, hc02, hlam, ht23, ht34, ht45]
                · linarith only [h0, h68, h81, h83, hc02, hlam, ht23, ht34, ht45]

theorem r1l7_12_14_25_L_R_L_I_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h2, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                · rcases h4bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h3, h6, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h6, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 4) (by simp) with h13 | h13
                    · rcases p9_3 (m.d 1 4) (by simp) with h14 | h14
                      · rcases p9_3 (m.d 2 4) (by simp) with h15 | h15
                        · linarith only [h0, h15, hlam]
                        · linarith only [h15, h5, hlam]
                      · linarith only [h14, h3, h6, h7, hlam]
                    · linarith only [h13, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 4) (by simp) with h20 | h20
                    · rcases p9_3 (m.d 1 4) (by simp) with h21 | h21
                      · rcases p9_3 (m.d 2 4) (by simp) with h22 | h22
                        · linarith only [h0, h22, hlam]
                        · linarith only [h22, h6, hlam]
                      · linarith only [h21, h3, h6, hlam]
                    · linarith only [h20, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h6, h7, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h3, h6, h7, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 4) (by simp) with h30 | h30
                    · rcases p9_3 (m.d 1 4) (by simp) with h31 | h31
                      · rcases p9_3 (m.d 2 4) (by simp) with h32 | h32
                        · linarith only [h3, h32, hlam]
                        · linarith only [h32, h5, hlam]
                      · linarith only [h31, hlam, p9_0]
                    · linarith only [h0, h30, h6, h7, hlam]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 4) (by simp) with h37 | h37
                    · rcases p9_3 (m.d 1 4) (by simp) with h38 | h38
                      · rcases p9_3 (m.d 2 4) (by simp) with h39 | h39
                        · linarith only [h3, h39, hlam]
                        · linarith only [h39, h6, hlam]
                      · linarith only [h38, hlam, p9_0]
                    · linarith only [h0, h37, h6, hlam]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h3, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 4) (by simp) with h47 | h47
                    · rcases p9_3 (m.d 1 4) (by simp) with h48 | h48
                      · rcases p9_3 (m.d 2 4) (by simp) with h49 | h49
                        · rcases p9_3 (m.d 3 4) (by simp) with h50 | h50
                          · linarith only [h5, h50, hlam]
                          · rcases p9_3 (m.d 4 5) (by simp) with h52 | h52
                            · linarith only [h52, h6, hlam]
                            · linarith only [h52, h7, hlam]
                        · linarith only [h49, h5, hlam]
                      · linarith only [h3, h48, h6, h7, hlam]
                    · linarith only [h0, h47, h6, h7, hlam]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h7, hc04, hc45, hlam, hphi, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h3, h6, h7, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h5, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h7, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h6, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h3, h6, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h6, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h2, h5, h6, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
              · linarith only [h6, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                · rcases h4bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, h70, hc04, hlam, hphi, ht0b, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h70, hc02, hlam, hphi, ht0b, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p72_1, u2ehi2]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    rcases p72_3 (m.d 0 4) (by simp) with h77 | h77
                    · rcases p72_3 (m.d 1 4) (by simp) with h78 | h78
                      · rcases p72_3 (m.d 2 4) (by simp) with h79 | h79
                        · linarith only [h0, h79, hlam]
                        · linarith only [h70, h79, hlam]
                      · linarith only [h3, h70, h78, hlam]
                    · linarith only [h77, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h70, hc14, hlam, hphi, ht01, ht0b, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, h70, hc12, hlam, hphi, ht01, ht0b, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p72_1, u2ehi2]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    rcases p72_3 (m.d 0 4) (by simp) with h88 | h88
                    · rcases p72_3 (m.d 1 4) (by simp) with h89 | h89
                      · rcases p72_3 (m.d 2 4) (by simp) with h90 | h90
                        · linarith only [h3, h90, hlam]
                        · linarith only [h70, h90, hlam]
                      · linarith only [h89, hlam, p72_0]
                    · linarith only [h0, h70, h88, hlam]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h5, hlam, p72_1]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, hc02, hlam, hphi, ht0b, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht23, p72_1, u2ehi3]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, h70, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h70, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p72_1, u5ehi9]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    rcases p72_3 (m.d 0 4) (by simp) with h104 | h104
                    · rcases p72_3 (m.d 1 4) (by simp) with h105 | h105
                      · rcases p72_3 (m.d 2 4) (by simp) with h106 | h106
                        · linarith only [h106, h5, hlam]
                        · linarith only [h106, h70, hlam]
                      · linarith only [h105, h3, h70, hlam]
                    · linarith only [h0, h104, h70, hlam]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h0, h70, hlam, p72_1]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h3, h70, hlam, p72_1]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h70, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [h71, hlam, p72_0]
                  · have p72_0 := h72c.1
                    have p72_1 := h72c.2.1
                    have p72_2 := h72c.2.2.1
                    have p72_3 := h72c.2.2.2
                    linarith only [hlam, p72_0]
                · linarith only [h0, h5, h70, h71, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h70, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h1, h4, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
        · linarith only [h120, h2, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
          · linarith only [h0, h120, h122, hc02, hlam, hphi, ht0b, ht5b, u5ehi7]
          · linarith only [h122, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h126 | h126
    · linarith only [h0, h126, hc24, hlam, hphi, u2ehi4]
    · linarith only [h126, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_12_24_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · rcases h4bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc14, hlam, hphi, p11_1, u4elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc24, hlam, hphi, p11_1, u4elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc34, hlam, hphi, p11_1, u4elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          rcases p11_3 (m.d 0 4) (by simp) with h16 | h16
                          · rcases p11_3 (m.d 1 4) (by simp) with h17 | h17
                            · rcases p11_3 (m.d 2 4) (by simp) with h18 | h18
                              · linarith only [h0, h18, hlam]
                              · linarith only [h18, h9, hlam]
                            · linarith only [h17, hc14, hlam, hphi, p11_1, u4elo0]
                          · linarith only [h16, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc04, hlam, hphi, p11_1, u4elo1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h9, hlam, hphi, ht23, ht34, p11_1, u2ehi4, u4elo1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p11_1, u4elo1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          rcases p11_3 (m.d 0 4) (by simp) with h27 | h27
                          · rcases p11_3 (m.d 1 4) (by simp) with h28 | h28
                            · rcases p11_3 (m.d 2 4) (by simp) with h29 | h29
                              · linarith only [h29, h4, hlam]
                              · linarith only [h29, h9, hlam]
                            · linarith only [h28, hlam, p11_0]
                          · linarith only [h2, h27, hlam]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h4, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p11_1, u4elo2]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          rcases p11_3 (m.d 0 4) (by simp) with h38 | h38
                          · rcases p11_3 (m.d 1 4) (by simp) with h39 | h39
                            · rcases p11_3 (m.d 2 4) (by simp) with h40 | h40
                              · rcases p11_3 (m.d 3 4) (by simp) with h41 | h41
                                · linarith only [h41, h7, hlam]
                                · linarith only [h10, h41, hlam]
                              · linarith only [h40, hlam, p11_0]
                            · linarith only [h39, h4, hlam, p11_1]
                          · linarith only [h2, h38, hlam]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc04, hlam, hphi, p11_1, u4elo3]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h6, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h3, h7, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h2, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h4, hc24, hlam, hphi, p11_1, u4elo4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h9, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                      · linarith only [h10, h2, hc34, hlam, hphi, u4elo0]
                    · linarith only [h2, h9, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h59, h7, h8, hlam]
                    · linarith only [h59, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                · linarith only [h7, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
              · linarith only [h3, h6, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h1, h2, h5, hlam, hphi, ht23, ht34, u2ehi1, u4elo0]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
          · linarith only [h3, h66, hc23, hlam, hphi, u2ehi3]
          · linarith only [h66, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
    · linarith only [h0, h1, hc25, hlam, hphi, u2ehi3]
  · linarith only [h0, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

end R2N4
