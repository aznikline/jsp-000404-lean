import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_LI_L_R_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h5, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                  · rcases h2bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hc12, hlam, hphi, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h10, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo1, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h10, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h1, hlam, p11_0]
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
                      linarith only [h6, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h8, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h2, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h5, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo3, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h3, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hc12, hlam, hphi, p11_1, u2elo4]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0, u3ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h10, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                  · rcases h2bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo1, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h0, h10, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h1, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h4, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h6, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h8, hlam, p37_1]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h2, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h5, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo3, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h10, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h3, hlam, p37_0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h3, hc12, hlam, hphi, p37_1, u2elo0]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [h3, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p37_1, u2elo0, u3ehi2]
                    · have p37_0 := h37c.1
                      have p37_1 := h37c.2.1
                      have p37_2 := h37c.2.2.1
                      have p37_3 := h37c.2.2.2
                      linarith only [hlam, p37_0]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
        · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
          · linarith only [h1, h69, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
            · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
              · linarith only [h0, h1, h71, h72, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
              · linarith only [h0, h1, h71, h72, hlam]
            · linarith only [h1, h67, h71, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
          · linarith only [h1, h76, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
            · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
              · linarith only [h0, h1, h78, h79, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
              · linarith only [h0, h1, h78, h79, hlam]
            · linarith only [h1, h67, h78, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h83 | h83
        · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
          · linarith only [h1, h84, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
            · linarith only [h0, h67, h86, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                · linarith only [h67, h83, h88, h89, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                · linarith only [h88, h89, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                · linarith only [h88, h92, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h83, h92, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
          · linarith only [h0, h1, h95, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
            · linarith only [h0, h67, h97, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
              · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                  · rcases h2bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h101, h83, h99, hc12, hlam, hphi, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h1, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h67, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h83, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h0, hlam, p102_1]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h95, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h97, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h83, hc02, hlam, hphi, p102_1, u2elo1]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hc12, hlam, hphi, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h101, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h0, h83, hc12, hlam, hphi, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p102_1, u2elo3]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hc12, hlam, hphi, p102_1, u2elo3]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h99, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h0, h83, h99, hc12, hlam, hphi, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p102_1, u2elo4]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h101, h99, hc12, hlam, hphi, p102_1, u2elo2]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h100, hlam, p102_0]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [h101, hlam, p102_1]
                    · have p102_0 := h102c.1
                      have p102_1 := h102c.2.1
                      have p102_2 := h102c.2.2.1
                      have p102_3 := h102c.2.2.2
                      linarith only [hlam, p102_0]
                  · rcases h2bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hc12, hlam, hphi, p128_1, u2elo0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h1, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h67, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h83, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, hlam, p128_1]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h95, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h97, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, h101, h67, h83, hc05, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p128_1]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hc02, hlam, hphi, p128_1, u2elo2]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hc12, hlam, hphi, p128_1, u2elo2]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, h67, hc12, hlam, hphi, p128_1, u2elo2]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, h83, hc12, hlam, hphi, p128_1, u2elo2]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p128_1, u2elo3]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hc12, hlam, hphi, p128_1, u2elo3]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h99, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h101, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p128_1, u2elo4]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h100, hc12, hlam, hphi, p128_1, u2elo2]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h100, hlam, p128_0]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [h0, h100, h67, hc12, hlam, hphi, p128_1, u2elo2]
                    · have p128_0 := h128c.1
                      have p128_1 := h128c.2.1
                      have p128_2 := h128c.2.2.1
                      have p128_3 := h128c.2.2.2
                      linarith only [hlam, p128_0]
                · linarith only [h100, h99, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                · linarith only [h155, h99, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                  · rcases h2bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hc12, hlam, hphi, p158_1, u2elo0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h1, hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h67, hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h83, hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h0, hlam, p158_1]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h95, hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h97, hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h1, h155, hc02, hlam, hphi, p158_1, u2elo1]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hc02, hlam, hphi, p158_1, u2elo2]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h155, h157, hc12, hlam, hphi, p158_1, u2elo3]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h99, hlam, p158_1]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h155, hlam, p158_1]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p158_1, u2elo3]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hc12, hlam, hphi, p158_1, u2elo3]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p158_1, u2elo3, u3ehi0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hlam, p158_0]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h0, h83, hc12, hlam, hphi, p158_1, u2elo3]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p158_1, u2elo4]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h157, hc12, hlam, hphi, p158_1, u2elo3]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h0, h1, h157, hc12, hlam, hphi, p158_1, u2elo3]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [h157, hlam, p158_1]
                    · have p158_0 := h158c.1
                      have p158_1 := h158c.2.1
                      have p158_2 := h158c.2.2.1
                      have p158_3 := h158c.2.2.2
                      linarith only [hlam, p158_0]
                  · rcases h2bigk with h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h1, hc12, hlam, hphi, p184_1, u2elo2]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h1, hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h67, hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h83, hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h0, hlam, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h95, hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h97, hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h0, h1, h157, h99, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h157, h99, hc02, hc45, hlam, hphi, ht23, ht34, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h157, h99, hc12, hc45, hlam, hphi, ht23, ht34, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h99, hlam, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h155, hlam, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h0, h157, hc12, hc45, hlam, hphi, ht23, ht34, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h157, hc12, hc45, hlam, hphi, ht23, ht34, p184_1]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h157, hc45, hlam, hphi, ht34, p184_1, u3ehi2]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h157, hlam, p184_0]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p184_1, u2elo4]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [hc12, hlam, hphi, p184_1, u2elo4]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h0, h1, hc12, hlam, hphi, p184_1, u2elo4]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [h0, h67, hc12, hlam, hphi, p184_1, u2elo4]
                    · have p184_0 := h184c.1
                      have p184_1 := h184c.2.1
                      have p184_2 := h184c.2.2.1
                      have p184_3 := h184c.2.2.2
                      linarith only [hlam, p184_0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h210 | h210
    · rcases m.htr 0 2 4 (by decide) (by decide) with h211 | h211
      · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
          · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
            · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
              · linarith only [h0, h210, h215, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h217 | h217
                · linarith only [h0, h211, h215, h217, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                  · rcases h2bigk with h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h0, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h0, h219, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p220_1, u2elo1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h0, h217, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hc02, hlam, hphi, p220_1, u2elo1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h215, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h217, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h210, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h213, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h215, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h217, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h211, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h214, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h211, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p220_1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h0, h211, h217, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h212, hlam, p220_0]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h0, hc02, hlam, hphi, p220_1, u2elo4]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h212, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p220_1, u3ehi2]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [h219, hlam, p220_1]
                    · have p220_0 := h220c.1
                      have p220_1 := h220c.2.1
                      have p220_2 := h220c.2.2.1
                      have p220_3 := h220c.2.2.2
                      linarith only [hlam, p220_0]
                  · rcases h2bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h215, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h217, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hc02, hlam, hphi, p246_1, u2elo1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h215, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h215, h219, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h210, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h213, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h215, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h217, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h211, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h214, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h212, h219, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h219, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h212, hlam, p246_0]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h212, hlam, p246_1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h212, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p246_1, u2elo1, u3ehi2]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [h0, h212, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p246_1, u2elo1]
                    · have p246_0 := h246c.1
                      have p246_1 := h246c.2.1
                      have p246_2 := h246c.2.2.1
                      have p246_3 := h246c.2.2.2
                      linarith only [hlam, p246_0]
            · linarith only [h0, h214, hc01, hlam, hphi, ht12, u2elo3]
          · linarith only [h0, h210, h213, hlam]
        · linarith only [h210, h212, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · linarith only [h210, h211, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h276 | h276
      · rcases m.htr 0 2 5 (by decide) (by decide) with h277 | h277
        · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
          · linarith only [h210, h278, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h278, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
          · linarith only [h210, h276, h281, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
          · linarith only [h0, h281, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h284 | h284
        · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
          · linarith only [h210, h284, h285, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
          · linarith only [h0, h285, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
          · linarith only [h210, h288, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h288, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_22_14_M_LI_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4ehi := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h5, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                  · rcases h2bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hc12, hlam, hphi, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      rcases p11_3 (m.d 0 2) (by simp) with h14 | h14
                      · rcases p11_3 (m.d 1 2) (by simp) with h15 | h15
                        · linarith only [h0, h15, hlam]
                        · linarith only [h15, h4, hlam]
                      · linarith only [h14, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0, u4ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0, u4ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      rcases p11_3 (m.d 0 2) (by simp) with h23 | h23
                      · rcases p11_3 (m.d 1 2) (by simp) with h24 | h24
                        · rcases p11_3 (m.d 2 3) (by simp) with h25 | h25
                          · linarith only [h25, hlam, p11_0]
                          · rcases p11_3 (m.d 2 4) (by simp) with h27 | h27
                            · linarith only [h27, h5, hlam]
                            · linarith only [h27, h7, hlam]
                        · linarith only [h24, hlam, p11_0]
                      · linarith only [h1, h23, hlam]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo1, u4ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0, u4ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h1, hlam, p11_0]
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
                      linarith only [h7, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo2, u4ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h2, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h5, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h9, hc23, hc45, hlam, hphi, ht34, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h9, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h3, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h6, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0, u4ehi2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
              · linarith only [h3, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h2, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h53 | h53
        · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
          · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
            · linarith only [h2, h55, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                · linarith only [h0, h2, h54, h58, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                  · linarith only [h2, h53, h60, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                  · linarith only [h0, h2, h54, h60, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2, h53, h54, h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h1, h2, h54, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
          · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
            · linarith only [h2, h66, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
              · linarith only [h0, h53, h68, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · linarith only [h0, h2, h65, h70, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                  · rcases h2bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h53, h72, hc12, hlam, hphi, p73_1, u2elo3]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h53, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo3]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h2, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h53, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h0, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h0, h53, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo3]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h66, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h68, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h1, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h65, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h70, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h53, hc02, hlam, hphi, p73_1, u2elo2]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo3]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo3]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      rcases p73_3 (m.d 0 2) (by simp) with h91 | h91
                      · linarith only [h2, h91, hlam]
                      · linarith only [h1, h91, hlam]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h0, h53, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo3]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h0, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo4]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p73_1, u2elo4]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      rcases p73_3 (m.d 0 2) (by simp) with h98 | h98
                      · linarith only [h53, h98, hlam]
                      · linarith only [h1, h98, hlam]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [h72, hlam, p73_0]
                    · have p73_0 := h73c.1
                      have p73_1 := h73c.2.1
                      have p73_2 := h73c.2.2.1
                      have p73_3 := h73c.2.2.2
                      linarith only [hlam, p73_0]
                  · linarith only [h0, h2, h65, h72, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1, h2, h65, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h105 | h105
      · linarith only [h1, h105, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
        · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
          · linarith only [h1, h108, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
            · linarith only [h0, h105, h110, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
              · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h0, h105, h112, h113, h114, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h0, h105, h112, h114, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h0, h1, h112, h117, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h0, h1, h112, h113, h117, hlam]
              · linarith only [h1, h107, h112, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
          · linarith only [h1, h121, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
            · linarith only [h0, h1, h123, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
              · linarith only [h0, h107, h125, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                  · rcases h2bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h107, h127, h128, hc12, hlam, hphi, p129_1, u2elo2]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h1, hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h105, hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h107, hlam, p129_0]
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
                      linarith only [h121, hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h123, hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h125, hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hc02, hlam, hphi, p129_1, u2elo2]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hc12, hlam, hphi, p129_1, u2elo2]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p129_1, u2elo2, u4ehi2]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h0, h107, hc12, hlam, hphi, p129_1, u2elo2]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p129_1, u2elo3]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hc12, hlam, hphi, p129_1, u2elo3]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h127, hlam, p129_1]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hlam, p129_0]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h0, h107, h127, hc12, hlam, hphi, p129_1, u2elo2]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p129_1, u2elo4]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [hc12, hlam, hphi, p129_1, u2elo4]
                    · have p129_0 := h129c.1
                      have p129_1 := h129c.2.1
                      have p129_2 := h129c.2.2.1
                      have p129_3 := h129c.2.2.2
                      linarith only [h127, h128, hlam, p129_1]
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
                  · rcases h2bigk with h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hc12, hlam, hphi, p155_1, u2elo0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h1, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h105, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h107, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h0, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h121, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h123, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h125, hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hc02, hlam, hphi, p155_1, u2elo2]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hc12, hlam, hphi, p155_1, u2elo2]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p155_1, u2elo2, u4ehi2]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h0, h107, hc12, hlam, hphi, p155_1, u2elo2]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p155_1, u2elo3]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hc12, hlam, hphi, p155_1, u2elo3]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h127, hlam, p155_1]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, p155_0]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h128, hlam, p155_1]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p155_1, u2elo4]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hc12, hlam, hphi, p155_1, u2elo4]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [h127, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p155_1, u2elo4, u4ehi3]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p155_1, u2elo4, u4ehi2]
                    · have p155_0 := h155c.1
                      have p155_1 := h155c.2.1
                      have p155_2 := h155c.2.2.1
                      have p155_3 := h155c.2.2.2
                      linarith only [hlam, p155_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                  · rcases h2bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hc12, hlam, hphi, p182_1, u2elo0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h1, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h105, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h107, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h121, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h123, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h125, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hc02, hlam, hphi, p182_1, u2elo2]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h127, hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h127, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, h107, h127, hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, h1, hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, h107, hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p182_1, u2elo4]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hc12, hlam, hphi, p182_1, u2elo4]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h0, h1, h181, hc12, hlam, hphi, p182_1, u2elo3]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [h181, hlam, p182_0]
                    · have p182_0 := h182c.1
                      have p182_1 := h182c.2.1
                      have p182_2 := h182c.2.2.1
                      have p182_3 := h182c.2.2.2
                      linarith only [hlam, p182_0]
                  · rcases h2bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h1, hc12, hlam, hphi, p208_1, u2elo2]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h1, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h105, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h107, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h0, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h121, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h123, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h125, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hc02, hlam, hphi, p208_1, u2elo2]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h127, hc12, hc34, hlam, hphi, ht23, p208_1]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h127, hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h0, h107, h127, h181, hc12, hc45, hlam, hphi, ht23, ht34, p208_1]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h0, h181, hc12, hc45, hlam, hphi, ht23, ht34, p208_1]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h181, hc12, hc45, hlam, hphi, ht23, ht34, p208_1]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h181, hc23, hc45, hlam, hphi, ht34, p208_1]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hlam, p208_0]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h181, hlam, p208_1]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p208_1, u2elo4]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hc12, hlam, hphi, p208_1, u2elo4]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [h0, h1, hc12, hlam, hphi, p208_1, u2elo4]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p208_1, u2elo4, u4ehi2]
                    · have p208_0 := h208c.1
                      have p208_1 := h208c.2.1
                      have p208_2 := h208c.2.2.1
                      have p208_3 := h208c.2.2.2
                      linarith only [hlam, p208_0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h234 | h234
    · rcases m.htr 0 2 4 (by decide) (by decide) with h235 | h235
      · rcases m.htr 0 2 5 (by decide) (by decide) with h236 | h236
        · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
          · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
            · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
              · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                · linarith only [h234, h240, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h235, h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                  · rcases h2bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h0, hlam, p244_1]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      rcases p244_3 (m.d 0 2) (by simp) with h247 | h247
                      · rcases p244_3 (m.d 1 2) (by simp) with h248 | h248
                        · rcases p244_3 (m.d 2 3) (by simp) with h249 | h249
                          · linarith only [h249, hlam, p244_0]
                          · rcases p244_3 (m.d 2 4) (by simp) with h251 | h251
                            · linarith only [h235, h251, hlam]
                            · linarith only [h240, h251, hlam]
                        · linarith only [h237, h248, hlam]
                      · linarith only [h247, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p244_1, u2elo1, u4ehi2]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h0, h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p244_1, u2elo1, u4ehi2]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hc02, hlam, hphi, p244_1, u2elo1]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      rcases p244_3 (m.d 0 2) (by simp) with h260 | h260
                      · linarith only [h0, h260, hlam]
                      · linarith only [h234, h260, hlam]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p244_1, u2elo1, u4ehi2]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p244_1, u2elo1, u4ehi2]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h234, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h237, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h240, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p244_1, u2elo2, u4ehi2]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h235, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h238, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h242, hc23, hc45, hlam, hphi, ht34, p244_1]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h242, hlam, p244_1]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h236, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h239, hlam, p244_0]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h0, h236, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p244_1, u2elo1]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [h0, h236, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p244_1, u2elo1, u4ehi2]
                    · have p244_0 := h244c.1
                      have p244_1 := h244c.2.1
                      have p244_2 := h244c.2.2.1
                      have p244_3 := h244c.2.2.2
                      linarith only [hlam, p244_0]
              · linarith only [h0, h236, h239, hlam]
            · linarith only [h0, h238, hc01, hlam, hphi, ht12, u2elo3]
          · linarith only [h0, h235, h237, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
        · linarith only [h235, h236, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h284 | h284
        · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
          · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
            · linarith only [h235, h286, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h286, hc01, hlam, hphi, ht12, u2elo3]
          · linarith only [h0, h285, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
          · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
            · linarith only [h235, h291, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h291, hc01, hlam, hphi, ht12, u2elo3]
          · linarith only [h0, h290, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h295 | h295
      · linarith only [h234, h295, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h297 | h297
        · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
          · linarith only [h234, h298, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h298, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
          · linarith only [h234, h301, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h301, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
