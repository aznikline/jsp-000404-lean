import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · rcases h0emin with h8 | h8 | h8 | h8 | h8
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
                      linarith only [h7, hc45, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc45, hlam, hphi, p9_1, u5elo0]
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
                      linarith only [h5, h7, hc45, hlam, hphi, p9_1, u5elo1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, h7, hc45, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc15, hlam, hphi, p9_1, u5elo2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9_1, u2elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9_1, u2elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc05, hlam, hphi, p9_1, u5elo3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, h5, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p9_1, u2elo0]
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
                      linarith only [h1, h5, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9_1, u2elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h3, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc15, hlam, hphi, p9_1, u5elo4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h6, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h7, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                  · linarith only [h8, hlam, ht01, ht12, u2elo0]
                  · linarith only [h8, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h8, hlam, ht01, ht12, u2elo0]
                  · linarith only [h8, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h1, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                · linarith only [h4, h40, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases h0emin with h42 | h42 | h42 | h42 | h42
                  · rcases h5bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hc15, hlam, hphi, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hc25, hlam, hphi, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h40, hc34, hlam, hphi, ht45, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h6, hc24, hlam, hphi, ht45, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h0, hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h4, h6, hc34, hlam, hphi, ht45, p43_1, u5elo1]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h0, h40, hc34, hlam, hphi, ht45, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h0, h4, h6, hc34, hlam, hphi, ht45, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h2, hlam, p43_1]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hc15, hlam, hphi, p43_1, u5elo2]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h40, hc34, hlam, hphi, ht45, p43_1, u5elo2]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h6, hlam, p43_1]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hc05, hlam, hphi, p43_1, u5elo3]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h3, h5, h6, hc15, hlam, hphi, p43_1, u5elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h5, hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h40, hlam, p43_1]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h3, hlam, p43_0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p43_1, u2elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h1, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p43_1, u2elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p43_1, u2elo0]
                    · have p43_0 := h43c.1
                      have p43_1 := h43c.2.1
                      have p43_2 := h43c.2.2.1
                      have p43_3 := h43c.2.2.2
                      linarith only [hlam, p43_0]
                  · linarith only [h42, hlam, ht01, ht12, u2elo0]
                  · linarith only [h42, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h42, hlam, ht01, ht12, u2elo0]
                  · linarith only [h42, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
            · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                · rcases h0emin with h77 | h77 | h77 | h77 | h77
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
                      linarith only [hc15, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hc25, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h76, hc45, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hc45, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h0, hlam, p78_0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hlam, p78_0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h74, h76, hc45, hlam, hphi, p78_1, u5elo1]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h0, h76, hc45, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h2, hlam, p78_1]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hc15, hlam, hphi, p78_1, u5elo2]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hlam, p78_0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h4, h74, h76, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p78_1, u3elo3]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h4, h74, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p78_1, u3elo3]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hc05, hlam, hphi, p78_1, u5elo3]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h2, h74, hc15, hlam, hphi, p78_1, u5elo0]
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
                      linarith only [h2, h74, hc45, hlam, hphi, p78_1, u5elo0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h3, hlam, p78_0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hc15, hlam, hphi, p78_1, u5elo4]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h75, hlam, p78_0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [h76, hlam, p78_0]
                    · have p78_0 := h78c.1
                      have p78_1 := h78c.2.1
                      have p78_2 := h78c.2.2.1
                      have p78_3 := h78c.2.2.2
                      linarith only [hlam, p78_0]
                  · linarith only [h77, hlam, ht01, ht12, u2elo0]
                  · linarith only [h77, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h77, hlam, ht01, ht12, u2elo0]
                  · linarith only [h77, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h1, h4, h75, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1, h3, h4, h74, h75, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
              · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                · rcases h0emin with h112 | h112 | h112 | h112 | h112
                  · rcases h5bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc15, hlam, hphi, p113_1, u5elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h74, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc35, hlam, hphi, p113_1, u5elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc45, hlam, hphi, p113_1, u5elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h0, hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h74, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo1]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h0, h74, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, p113_1, u5elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h2, hlam, p113_1]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc15, hlam, hphi, p113_1, u5elo2]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h74, hlam, p113_1]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h1, h110, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p113_1, u2elo0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc05, hlam, hphi, p113_1, u5elo3]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc15, hlam, hphi, p113_1, u5elo3]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h74, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo3]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc45, hlam, hphi, p113_1, u5elo3]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h3, hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hc15, hlam, hphi, p113_1, u5elo4]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h110, hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [h111, hlam, p113_0]
                    · have p113_0 := h113c.1
                      have p113_1 := h113c.2.1
                      have p113_2 := h113c.2.2.1
                      have p113_3 := h113c.2.2.2
                      linarith only [hlam, p113_0]
                  · linarith only [h112, hlam, ht01, ht12, u2elo0]
                  · linarith only [h112, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h112, hlam, ht01, ht12, u2elo0]
                  · linarith only [h112, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h1, h110, h111, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                · linarith only [h110, h144, h4, hc23, hlam, hphi, u3elo3]
                · linarith only [h1, h144, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
          · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
            · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
              · linarith only [h1, h149, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                · linarith only [h1, h147, h151, h3, hlam]
                · rcases h0emin with h153 | h153 | h153 | h153 | h153
                  · rcases h5bigk with h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hlam, p154_0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hc15, hlam, hphi, p154_1, u5elo0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h3, hc25, hlam, hphi, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h151, h3, hc34, hlam, hphi, ht45, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h3, hlam, p154_1]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h0, hlam, p154_0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hlam, p154_0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h148, h151, hc34, hlam, hphi, ht45, p154_1, u5elo1]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h0, h151, h3, hc34, hlam, hphi, ht45, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h0, h3, hlam, p154_1]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h2, hlam, p154_1]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hc15, hlam, hphi, p154_1, u5elo2]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hlam, p154_0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h151, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p154_1, u2elo0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h149, hlam, p154_1]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hc05, hlam, hphi, p154_1, u5elo3]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h148, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p154_1, u3elo2]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h148, hlam, p154_0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hlam, p154_0]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h151, hlam, p154_1]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hc05, hlam, hphi, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hc15, hlam, hphi, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h147, h149, hc34, hlam, hphi, ht45, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [h151, hc34, hlam, hphi, ht45, p154_1, u5elo4]
                    · have p154_0 := h154c.1
                      have p154_1 := h154c.2.1
                      have p154_2 := h154c.2.2.1
                      have p154_3 := h154c.2.2.2
                      linarith only [hlam, p154_0]
                  · linarith only [h153, hlam, ht01, ht12, u2elo0]
                  · linarith only [h153, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h153, h3, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h153, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h147, h148, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
            · linarith only [h1, h147, h185, h3, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
              · linarith only [h1, h187, h3, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                · linarith only [h1, h147, h189, h3, hc23, hlam, hphi, u3elo3]
                · linarith only [h147, h189, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h1, h2, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h193 | h193
      · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
        · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
          · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
            · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
              · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                · rcases h0emin with h199 | h199 | h199 | h199 | h199
                  · rcases h5bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, h198, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h0, hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h196, h198, hc45, hlam, hphi, p200_1, u5elo1]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h0, h1, h193, h195, h198, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h0, h1, h193, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h193, hlam, p200_1]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hc15, hlam, hphi, p200_1, u5elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, h198, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hc05, hlam, hphi, p200_1, u5elo3]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, h196, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h196, hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h1, h193, h195, h196, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo2]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h194, hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h198, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p200_1, u3elo3]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h197, hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [h198, hlam, p200_0]
                    · have p200_0 := h200c.1
                      have p200_1 := h200c.2.1
                      have p200_2 := h200c.2.2.1
                      have p200_3 := h200c.2.2.2
                      linarith only [hlam, p200_0]
                  · linarith only [h1, h195, h199, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h199, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h195, h199, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h199, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h1, h193, h195, h197, h198, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1, h197, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h1, h195, h196, hc02, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
            · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
              · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                · rcases h0emin with h236 | h236 | h236 | h236 | h236
                  · rcases h5bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h1, h193, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p237_1, u2elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h1, h193, h233, h235, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p237_1, u2elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h1, h193, h195, h235, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h1, h193, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h0, hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h233, h235, hc45, hlam, hphi, p237_1, u5elo1]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h0, h1, h193, h195, h235, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h0, h1, h193, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h193, hlam, p237_1]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hc15, hlam, hphi, p237_1, u5elo2]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h1, h193, h195, h235, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h1, h193, h195, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p237_1, u3elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hc05, hlam, hphi, p237_1, u5elo3]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h193, h233, hc15, hlam, hphi, p237_1, u5elo0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h233, hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h193, h233, hc45, hlam, hphi, p237_1, u5elo0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h194, hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hc15, hlam, hphi, p237_1, u5elo4]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h234, hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [h235, hlam, p237_0]
                    · have p237_0 := h237c.1
                      have p237_1 := h237c.2.1
                      have p237_2 := h237c.2.2.1
                      have p237_3 := h237c.2.2.2
                      linarith only [hlam, p237_0]
                  · linarith only [h1, h195, h236, hlam, ht01, ht12, ht23, u3elo3]
                  · linarith only [h236, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h195, h236, hlam, ht01, ht12, ht23, u3elo3]
                  · linarith only [h1, h193, h195, h236, hlam, ht01, ht12, ht23, u3elo3]
                · linarith only [h1, h193, h195, h234, h235, hlam]
              · linarith only [h1, h234, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h1, h193, h195, h233, hc23, hlam, hphi, u3elo3]
        · linarith only [h1, h193, h194, hc25, hlam, hphi, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h271 | h271
        · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
          · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
            · rcases m.htr 2 4 5 (by decide) (by decide) with h274 | h274
              · rcases m.htr 3 4 5 (by decide) (by decide) with h275 | h275
                · rcases h0emin with h276 | h276 | h276 | h276 | h276
                  · rcases h5bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hc15, hlam, hphi, p277_1, u5elo0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h193, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h193, hc35, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h193, hc45, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h193, hc02, hlam, hphi, ht23, ht34, ht45, p277_1, u5elo1]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, h275, hc45, hlam, hphi, p277_1, u5elo0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, h193, hc45, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hc05, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hc15, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h275, hc45, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hc45, hlam, hphi, p277_1, u5elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h193, hc02, hlam, hphi, ht23, p277_1, u3elo4]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h272, h275, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p277_1, u3elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h273, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h272, h275, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p277_1, u3elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h271, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hc15, hlam, hphi, p277_1, u5elo4]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h274, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h275, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                  · linarith only [h276, hlam, ht01, ht12, u2elo0]
                  · linarith only [h276, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h272, h276, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h276, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · rcases h0emin with h307 | h307 | h307 | h307 | h307
                  · rcases h5bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h193, hc15, hlam, hphi, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h193, hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h193, hc35, hlam, hphi, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h193, h275, hc34, hlam, hphi, ht45, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h0, hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h1, h193, h271, h272, h275, hc02, hc34, hlam, hphi, ht23, ht45, p308_1, u3elo2, u5elo1]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h0, h275, hc34, hlam, hphi, ht45, p308_1, u5elo0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h0, h193, h275, hc34, hlam, hphi, ht45, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hc05, hlam, hphi, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hc15, hlam, hphi, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h275, hc34, hlam, hphi, ht45, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h275, hc34, hlam, hphi, ht45, p308_1, u5elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h271, h275, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p308_1, u3elo4]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h1, h271, h275, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p308_1, u2elo3]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h273, hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h275, hlam, p308_1]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h271, hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h1, h271, h272, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p308_1, u3elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h274, hlam, p308_0]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [h1, h271, h272, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p308_1, u3elo2]
                    · have p308_0 := h308c.1
                      have p308_1 := h308c.2.1
                      have p308_2 := h308c.2.2.1
                      have p308_3 := h308c.2.2.2
                      linarith only [hlam, p308_0]
                  · linarith only [h307, hlam, ht01, ht12, u2elo0]
                  · linarith only [h307, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h272, h307, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h307, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h1, h271, h274, hlam]
            · linarith only [h1, h271, h272, h273, hc45, hlam, hphi, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h340 | h340
            · linarith only [h193, h272, h340, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h342 | h342
              · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                · rcases h0emin with h344 | h344 | h344 | h344 | h344
                  · rcases h5bigk with h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hc15, hlam, hphi, p345_1, u5elo0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h193, hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h193, h340, hlam, p345_1]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h193, h340, hc45, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h0, hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h193, hc02, hlam, hphi, ht23, ht34, ht45, p345_1, u5elo1]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h0, h193, h340, hlam, p345_1]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h0, h193, h340, hc45, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h340, hc05, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h340, hc15, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h340, hlam, p345_1]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h340, hc45, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h193, hc02, hlam, hphi, ht23, ht34, ht45, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hc15, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hc25, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hc45, hlam, hphi, p345_1, u5elo3]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h271, hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hc15, hlam, hphi, p345_1, u5elo4]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h342, hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [h343, hlam, p345_0]
                    · have p345_0 := h345c.1
                      have p345_1 := h345c.2.1
                      have p345_2 := h345c.2.2.1
                      have p345_3 := h345c.2.2.2
                      linarith only [hlam, p345_0]
                  · linarith only [h193, h342, h344, hlam, ht01, ht12, u2elo3]
                  · linarith only [h344, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h1, h344, hlam, ht01, ht12, u2elo3]
                  · linarith only [h344, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h1, h271, h272, h343, hlam]
              · linarith only [h1, h271, h342, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
          · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
            · rcases m.htr 2 4 5 (by decide) (by decide) with h379 | h379
              · linarith only [h1, h271, h377, h379, hc02, hlam, hphi, u2elo2]
              · linarith only [h1, h379, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h377, h378, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h383 | h383
            · linarith only [h193, h377, h383, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h385 | h385
              · linarith only [h1, h271, h385, hc02, hlam, hphi, u2elo3]
              · linarith only [h1, h385, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h388 | h388
    · rcases m.htr 0 2 5 (by decide) (by decide) with h389 | h389
      · rcases m.htr 0 4 5 (by decide) (by decide) with h390 | h390
        · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
          · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
            · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
              · rcases m.htr 3 4 5 (by decide) (by decide) with h394 | h394
                · rcases h0emin with h395 | h395 | h395 | h395 | h395
                  · linarith only [h0, h395, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h395, hlam, ht01, ht12, u2elo0]
                  · linarith only [h395, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h395, hlam, ht01, ht12, u2elo0]
                  · linarith only [h0, h395, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h388, h393, h394, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                · linarith only [h391, h393, h402, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases h0emin with h404 | h404 | h404 | h404 | h404
                  · linarith only [h0, h404, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h404, hlam, ht01, ht12, u2elo0]
                  · linarith only [h404, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h404, hlam, ht01, ht12, u2elo0]
                  · linarith only [h0, h404, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
            · linarith only [h391, h392, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h411 | h411
            · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
              · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                · rcases h0emin with h414 | h414 | h414 | h414 | h414
                  · linarith only [h0, h414, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h414, hlam, ht01, ht12, u2elo0]
                  · linarith only [h414, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h414, hlam, ht01, ht12, u2elo0]
                  · linarith only [h0, h414, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h391, h411, h413, hc35, hlam, hphi, u5elo4]
              · linarith only [h388, h390, h391, h411, h412, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h422 | h422
              · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
                · rcases h0emin with h424 | h424 | h424 | h424 | h424
                  · linarith only [h0, h424, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h424, hlam, ht01, ht12, u2elo0]
                  · linarith only [h424, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h424, hlam, ht01, ht12, u2elo0]
                  · linarith only [h0, h424, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h388, h422, h423, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h431 | h431
                · linarith only [h391, h422, h431, hc23, hlam, hphi, u3elo3]
                · linarith only [h388, h390, h391, h431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
          · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
            · rcases m.htr 2 4 5 (by decide) (by decide) with h436 | h436
              · linarith only [h388, h390, h436, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h438 | h438
                · linarith only [h0, h390, h434, h438, hc01, hlam, hphi, ht12, u2elo2]
                · rcases h0emin with h440 | h440 | h440 | h440 | h440
                  · linarith only [h0, h440, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h440, hlam, ht01, ht12, u2elo0]
                  · linarith only [h440, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h390, h440, hc45, hlam, ht01, ht12, ht23, ht34]
                  · linarith only [h440, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h434, h435, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
            · linarith only [h388, h390, h434, h447, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
              · linarith only [h388, h390, h449, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                · linarith only [h388, h390, h434, h451, hc23, hlam, hphi, u3elo3]
                · linarith only [h434, h451, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h388, h389, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h455 | h455
      · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
        · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
          · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
            · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
              · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                · rcases h0emin with h461 | h461 | h461 | h461 | h461
                  · linarith only [h0, h388, h455, h457, h458, h460, h461, hc45, hlam, hphi, ht01, ht12, ht23, u3elo2, u5elo1]
                  · linarith only [h388, h457, h461, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h461, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h457, h461, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h388, h455, h457, h461, hlam, ht01, ht12, ht23, u3elo2]
                · linarith only [h388, h455, h457, h459, h460, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h388, h459, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h388, h455, h457, h458, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h470 | h470
            · rcases m.htr 2 4 5 (by decide) (by decide) with h471 | h471
              · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                · rcases h0emin with h473 | h473 | h473 | h473 | h473
                  · linarith only [h0, h473, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h388, h473, hlam, ht01, ht12, u2elo3]
                  · linarith only [h473, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h473, hlam, ht01, ht12, u2elo3]
                  · linarith only [h388, h455, h473, hlam, ht01, ht12, u2elo3]
                · linarith only [h388, h455, h457, h470, h472, hc35, hlam, hphi, u5elo4]
              · linarith only [h388, h455, h456, h471, hlam]
            · linarith only [h388, h455, h457, h470, hc23, hlam, hphi, u3elo3]
        · linarith only [h388, h455, h456, hc25, hlam, hphi, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h483 | h483
        · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
          · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
            · rcases m.htr 2 4 5 (by decide) (by decide) with h486 | h486
              · rcases m.htr 3 4 5 (by decide) (by decide) with h487 | h487
                · rcases h0emin with h488 | h488 | h488 | h488 | h488
                  · linarith only [h0, h488, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h455, h488, hlam, ht01, ht12, u2elo4]
                  · linarith only [h488, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h484, h488, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h0, h488, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                · rcases h0emin with h494 | h494 | h494 | h494 | h494
                  · linarith only [h0, h388, h483, h484, h487, h494, hc34, hlam, hphi, ht01, ht12, ht23, ht45, u3elo2, u5elo1]
                  · linarith only [h388, h455, h483, h484, h487, h494, hc34, hlam, hphi, ht01, ht12, ht23, ht45, u3elo2, u5elo2]
                  · linarith only [h494, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h484, h494, hlam, ht01, ht12, ht23, u3elo2]
                  · linarith only [h0, h388, h483, h484, h487, h494, hc34, hlam, hphi, ht01, ht12, ht23, ht45, u3elo2, u5elo1]
              · linarith only [h388, h483, h486, hlam]
            · linarith only [h388, h483, h484, h485, hc45, hlam, hphi, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
            · linarith only [h455, h484, h502, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h504 | h504
              · rcases m.htr 3 4 5 (by decide) (by decide) with h505 | h505
                · rcases h0emin with h506 | h506 | h506 | h506 | h506
                  · linarith only [h0, h506, hlam, ht01, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h506, hlam, ht01, ht12, u2elo0]
                  · linarith only [h506, hlam, ht01, ht12, ht23, u3elo0]
                  · linarith only [h388, h506, hlam, ht01, ht12, u2elo3]
                  · linarith only [h455, h502, h506, hlam, ht01, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h388, h484, h505, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h388, h483, h504, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
          · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
            · rcases m.htr 2 4 5 (by decide) (by decide) with h516 | h516
              · linarith only [h388, h483, h516, hc02, hlam, hphi, u2elo3]
              · linarith only [h388, h516, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h514, h515, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
            · linarith only [h455, h514, h520, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
              · linarith only [h388, h483, h522, hc02, hlam, hphi, u2elo3]
              · linarith only [h388, h522, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]

end R2N4
