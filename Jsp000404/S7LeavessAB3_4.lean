import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB3_H_I_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · rcases h4bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h1, hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h12, h9, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p13_1]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h1, h12, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h1, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h2, hlam, p13_1]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h2, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h0, h12, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h0, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h3, hlam, p13_1]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h7, hlam, p13_1]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h9, hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo3]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h4, hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h8, hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h11, hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [h12, hlam, p13_0]
                            · obtain ⟨p13_0, p13_1, p13_2, p13_3⟩ := h13c
                              linarith only [hlam, p13_0]
                          · linarith only [h12, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h11, h4, hc24, hlam, hphi, ht45, u5elo0]
                      · linarith only [h10, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h3, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h8, hc14, hlam, hphi, ht45, u5elo0]
                · linarith only [h3, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                          · rcases h4bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h3, h47, h52, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h3, h49, h52, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h3, h52, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h1, hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h49, h52, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p53_1]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h47, h52, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p53_1]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h0, h47, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h2, hlam, p53_1]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h2, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p53_1]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h2, h3, h52, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h3, hlam, p53_1]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h47, hlam, p53_1]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h49, hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p53_1, u3elo3]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h4, hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h48, hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h51, hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [h52, hlam, p53_0]
                            · obtain ⟨p53_0, p53_1, p53_2, p53_3⟩ := h53c
                              linarith only [hlam, p53_0]
                          · linarith only [h52, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h4, h51, hc24, hlam, hphi, ht45, u5elo0]
                      · linarith only [h5, h50, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h46, h47, h49, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h4, h48, hc14, hlam, hphi, ht45, u5elo0]
                · linarith only [h3, h47, hc13, hlam, hphi, u3elo0]
              · linarith only [h46, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h4, hc04, hlam, hphi, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
          · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
            · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
              · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                · linarith only [h0, h3, h90, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                    · linarith only [h3, h93, hc03, hlam, hphi, u3elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                          · rcases h4bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h88, h90, h95, h97, hc04, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h3, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h1, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h93, h95, h97, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p98_1]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h90, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h1, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h2, hlam, p98_1]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h2, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h93, hlam, p98_1]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h88, h90, h95, h97, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p98_1, u3elo3]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h87, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h92, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h96, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [h97, hlam, p98_0]
                            · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                              linarith only [hlam, p98_0]
                          · linarith only [h97, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h93, h96, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h95, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h87, h92, hc14, hlam, hphi, ht45, u5elo0]
              · linarith only [h89, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
              · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                · linarith only [h0, h130, h3, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                    · linarith only [h0, h129, h133, h3, h88, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h129, h133, h88, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h132, h87, hc14, hlam, hphi, ht45, u5elo0]
              · linarith only [h129, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h87, hc04, hlam, hphi, ht45, u5elo4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
        · rcases m.htr 0 4 5 (by decide) (by decide) with h140 | h140
          · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
            · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
              · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                          · rcases h4bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h143, h148, hc04, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h2, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h139, h148, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p149_1, u3elo0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h139, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p149_1, u3elo0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h1, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h1, h2, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h148, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h2, hc02, hc24, hlam, hphi, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h141, h143, h145, h148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h0, h141, h145, h148, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p149_1, u3elo0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h0, h141, h145, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p149_1, u3elo0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h139, hlam, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h143, hlam, p149_1]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h145, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p149_1, u3elo3]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h140, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h144, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h147, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [h148, hlam, p149_0]
                            · obtain ⟨p149_0, p149_1, p149_2, p149_3⟩ := h149c
                              linarith only [hlam, p149_0]
                          · linarith only [h148, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h140, h147, h2, hc04, hlam, hphi, ht45, u5elo0]
                      · linarith only [h146, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h139, h145, hc23, hlam, hphi, u3elo0]
                  · linarith only [h144, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h139, h143, hc13, hlam, hphi, u3elo0]
              · linarith only [h142, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
              · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                          · rcases h4bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h183, h188, hc04, hc45, hlam, hphi, ht0b, ht5b, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h2, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h139, h188, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p189_1, u3elo0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h139, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p189_1, u3elo0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h1, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h1, h2, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h188, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h2, hc02, hc24, hlam, hphi, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h183, h185, h188, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p189_1, u3elo2]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h185, h188, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p189_1, u3elo2]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h185, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p189_1, u3elo2]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h139, hlam, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h183, hlam, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h185, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h183, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p189_1]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h140, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h184, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h187, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [h188, hlam, p189_0]
                            · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                              linarith only [hlam, p189_0]
                          · linarith only [h188, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h140, h187, h2, hc04, hlam, hphi, ht45, u5elo0]
                      · linarith only [h186, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h141, h185, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h184, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h139, h183, hc13, hlam, hphi, u3elo0]
              · linarith only [h182, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h140, hc04, hlam, hphi, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
          · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
            · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
              · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
                · linarith only [h0, h139, h226, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
                    · linarith only [h0, h139, h224, h229, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h231 | h231
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                          · rcases h4bigk with h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h224, h226, h231, h233, hc04, hc45, hlam, hphi, ht0b, ht5b, p234_1]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h2, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h139, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h2, h229, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h1, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p234_1]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h226, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h1, h139, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h2, hc02, hc24, hlam, hphi, p234_1]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h229, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h229, hlam, p234_1]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h229, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h0, h139, h224, h231, h233, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h224, h226, h231, h233, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p234_1, u3elo3]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h223, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h228, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h232, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [h233, hlam, p234_0]
                            · obtain ⟨p234_0, p234_1, p234_2, p234_3⟩ := h234c
                              linarith only [hlam, p234_0]
                          · linarith only [h233, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h2, h232, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h231, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h223, h228, hc14, hlam, hphi, ht45, u5elo0]
              · linarith only [h225, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
              · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
                · linarith only [h0, h139, h266, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                    · linarith only [h0, h139, h224, h265, h269, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h224, h265, h269, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h224, h265, h266, h268, hc25, hlam, hphi, u5elo4]
              · linarith only [h265, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h139, h223, hc13, hlam, hphi, ht34, ht45, u5elo4]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h275 | h275
      · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
        · linarith only [h0, h1, h276, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h278 | h278
          · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
            · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                · linarith only [h276, h281, hc03, hlam, hphi, u3elo1]
                · linarith only [h0, h1, h281, hc13, hlam, hphi, u3elo3]
              · linarith only [h279, h280, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                · linarith only [h0, h1, h276, h286, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1, h279, h285, h286, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h285, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h1, h278, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
        · linarith only [h0, h1, h291, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
          · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
            · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
              · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                · linarith only [h0, h1, h291, h296, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1, h294, h296, hc23, hlam, hphi, u3elo3]
              · linarith only [h294, h295, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
              · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
                · linarith only [h0, h1, h291, h301, hlam]
                · linarith only [h0, h1, h301, hc13, hlam, hphi, u3elo3]
              · linarith only [h300, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h1, h293, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h306 | h306
    · rcases m.htr 0 2 4 (by decide) (by decide) with h307 | h307
      · rcases m.htr 0 3 4 (by decide) (by decide) with h308 | h308
        · rcases m.htr 0 4 5 (by decide) (by decide) with h309 | h309
          · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
            · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
              · rcases m.htr 1 3 4 (by decide) (by decide) with h312 | h312
                · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
                  · linarith only [h0, h306, h313, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h312, h313, hc34, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h312, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h311, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                · rcases m.htr 1 4 5 (by decide) (by decide) with h320 | h320
                  · linarith only [h0, h306, h310, h320, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h319, h320, hc34, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h306, h319, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h318, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h309, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h0, h306, h308, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h327 | h327
        · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
          · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
            · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
              · rcases m.htr 1 3 4 (by decide) (by decide) with h331 | h331
                · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h0, h306, h332, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h331, h332, hc34, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h331, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h330, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h337 | h337
              · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                · rcases m.htr 1 4 5 (by decide) (by decide) with h339 | h339
                  · linarith only [h0, h306, h329, h339, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h338, h339, hc34, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h306, h338, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h337, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h328, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h0, h306, h327, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h346 | h346
      · rcases m.htr 0 3 4 (by decide) (by decide) with h347 | h347
        · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
          · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
            · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
              · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                          · rcases h4bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h306, hlam, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h306, h351, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h306, h351, h356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h306, h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h351, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h351, h353, h356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h351, h356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1, u3elo1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h346, hlam, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h346, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h356, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h346, hc02, hc45, hlam, hphi, ht0b, ht5b, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h347, hlam, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h351, hlam, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h353, hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h347, hc03, hc45, hlam, hphi, ht0b, ht5b, p357_1]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h348, hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h352, hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h355, hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [h356, hlam, p357_0]
                            · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                              linarith only [hlam, p357_0]
                          · linarith only [h356, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h348, h355, hc24, hlam, hphi, ht45, u5elo0]
                      · linarith only [h354, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h347, h353, hc23, hlam, hphi, u3elo1]
                  · linarith only [h306, h348, h352, hc04, hlam, hphi, ht45, u5elo0]
                · linarith only [h0, h351, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h350, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
              · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h396 | h396
                          · rcases h4bigk with h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h306, hlam, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h393, h396, hc04, hc45, hlam, hphi, ht0b, ht5b, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h0, h347, h349, h396, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h0, h347, h349, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h306, hc01, hc14, hlam, hphi, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h349, h391, h393, h396, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h349, h391, h396, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h349, h391, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h346, hlam, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h306, h346, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h0, h346, h347, h349, h396, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h0, h346, h347, h349, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo2]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h347, hlam, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h391, hlam, p397_1]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h393, hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p397_1, u3elo3]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h348, hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h392, hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h395, hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [h396, hlam, p397_0]
                            · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                              linarith only [hlam, p397_0]
                          · linarith only [h396, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h348, h395, hc24, hlam, hphi, ht45, u5elo0]
                      · linarith only [h0, h349, h394, hc03, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h347, h349, h390, h393, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h306, h392, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h347, h391, hlam]
              · linarith only [h390, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h348, hc04, hlam, hphi, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h431 | h431
          · rcases m.htr 1 2 3 (by decide) (by decide) with h432 | h432
            · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
              · rcases m.htr 1 3 4 (by decide) (by decide) with h434 | h434
                · linarith only [h0, h347, h434, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h434, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h433, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h438 | h438
              · rcases m.htr 1 3 4 (by decide) (by decide) with h439 | h439
                · linarith only [h0, h347, h439, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h439, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h438, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h431, hc04, hlam, hphi, ht45, u5elo4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h444 | h444
        · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
          · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
            · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
              · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                          · rcases h4bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h306, hlam, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h346, hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h453, hc04, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h346, h446, h450, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h306, hc01, hc14, hlam, hphi, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h448, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h448, h453, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h448, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h444, h453, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h446, h450, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h446, h450, h453, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h446, h450, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1, u3elo1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h444, hlam, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h448, hlam, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h450, hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h444, hc03, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h445, hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h449, hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h452, hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [h453, hlam, p454_0]
                            · obtain ⟨p454_0, p454_1, p454_2, p454_3⟩ := h454c
                              linarith only [hlam, p454_0]
                          · linarith only [h453, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h346, h445, h452, hc04, hlam, hphi, ht45, u5elo0]
                      · linarith only [h451, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h444, h450, hc23, hlam, hphi, u3elo1]
                  · linarith only [h306, h449, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h444, h448, hlam]
              · linarith only [h0, h446, h447, hc03, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
              · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h493 | h493
                          · rcases h4bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h306, hlam, p494_1]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h346, hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h493, hc04, hc45, hlam, hphi, ht0b, ht5b, p494_1]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h0, h444, h446, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h306, hc01, hc14, hlam, hphi, p494_1]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h446, h488, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h446, h488, h493, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h446, h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h444, h493, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p494_1]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h490, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h490, h493, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h490, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p494_1, u3elo2]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h444, hlam, p494_1]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h488, hlam, p494_1]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h490, hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p494_1, u3elo3]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h445, hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h489, hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h492, hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [h493, hlam, p494_0]
                            · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                              linarith only [hlam, p494_0]
                          · linarith only [h445, h493, hc34, hlam, hphi, ht45, u5elo0]
                        · linarith only [h445, h492, hc24, hlam, hphi, ht45, u5elo0]
                      · linarith only [h446, h491, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h446, h487, h490, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h306, h489, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h444, h488, hlam]
              · linarith only [h487, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h445, hc04, hlam, hphi, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
          · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
            · rcases m.htr 1 2 5 (by decide) (by decide) with h530 | h530
              · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
                · linarith only [h0, h444, h531, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h531, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h530, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h535 | h535
              · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                · linarith only [h0, h444, h536, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h536, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h535, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h528, hc04, hlam, hphi, ht45, u5elo4]

theorem n7l_sAB3_H_I_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h3elo := hb3.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
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
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h11, h4, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h14, h4, hc23, hlam, hphi, u3elo0]
                    · linarith only [h4, h9, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h18, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h18, h4, hc13, hlam, hphi, u3elo0]
                · linarith only [h3, h4, h6, h7, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                · linarith only [h22, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                            · linarith only [h24, h29, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                            · rcases h5bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p31_1, u3elo0, u5ehi1]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h22, h4, hc12, hlam, hphi, ht23, p31_1, u3elo0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p31_1, u3elo0, u5ehi3]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h29, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p31_1, u3elo0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h2, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h22, hlam, p31_1]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p31_1, u5ehi3]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h22, h29, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p31_1, u3elo0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h3, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p31_1, u3elo0, u5ehi1]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p31_1, u3elo0, u5ehi3]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h29, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p31_1, u3elo0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h4, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h25, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h27, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h29, hlam, p31_1]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h5, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h26, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h28, hlam, p31_0]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [h26, hc14, hlam, hphi, ht01, ht0b, ht5b, p31_1, u5ehi3]
                              · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                linarith only [hlam, p31_0]
                          · linarith only [h1, h22, h24, h26, h28, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h27, h4, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                            · linarith only [h1, h24, h26, h61, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases h5bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h25, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h22, h4, hc12, hlam, hphi, ht23, p63_1, u3elo0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h25, h26, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h2, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h22, hlam, p63_1]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h26, h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p63_1, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h26, hlam, p63_1]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h3, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p63_1, u5ehi1]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h26, h3, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p63_1, u3elo0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h4, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h25, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h59, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h61, hlam, p63_1]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h5, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h25, h5, hc04, hlam, hphi, ht0b, ht5b, p63_1, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h60, hlam, p63_0]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [h3, h4, h60, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0, u5ehi3]
                              · obtain ⟨p63_0, p63_1, p63_2, p63_3⟩ := h63c
                                linarith only [hlam, p63_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                            · linarith only [h22, h60, h89, hc12, hlam, hphi, ht23, u3elo3]
                            · rcases h5bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h25, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p91_1, u3elo0, u5ehi3]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h22, h4, hc12, hlam, hphi, ht23, p91_1, u3elo0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p91_1, u3elo0, u5ehi3]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h22, h4, h60, hc12, hlam, hphi, ht23, p91_1, u3elo0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h2, hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h22, hlam, p91_1]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi3]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h26, hlam, p91_1]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h3, hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p91_1, u5ehi1]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h4, h5, h60, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p91_1, u3elo0, u5ehi3]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h60, hlam, p91_1]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h4, hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h25, hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h59, hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h89, hlam, p91_1]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h5, hlam, p91_0]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p91_1, u3elo0, u5ehi1]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p91_1, u3elo0, u5ehi2]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p91_1, u3elo0, u5ehi3]
                              · obtain ⟨p91_0, p91_1, p91_2, p91_3⟩ := h91c
                                linarith only [hlam, p91_0]
                        · linarith only [h4, h59, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h24, h25, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h119, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h119, h4, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h126, h2, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                        · linarith only [h0, h122, h128, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h128, h4, hc23, hlam, hphi, u3elo0]
                    · linarith only [h125, h4, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                    · linarith only [h124, h132, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h132, h4, hc13, hlam, hphi, u3elo0]
                · linarith only [h122, h123, h3, h4, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h136 | h136
                · linarith only [h122, h136, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                      · linarith only [h1, h136, h138, h140, h3, h5, hc12, hlam, hphi, ht23, u3elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
                          · linarith only [h143, h3, h5, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h145 | h145
                            · linarith only [h136, h145, h3, h5, hc12, hlam, hphi, ht23, u3elo3]
                            · rcases h5bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h139, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p147_1, u3elo0, u5ehi3]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h136, h5, hc12, hc45, hlam, hphi, ht23, ht34, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p147_1, u3elo0, u5ehi3]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h5, hlam, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h2, hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h136, hlam, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p147_1, u5ehi3]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h140, hlam, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h3, hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p147_1, u5ehi1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p147_1, u3elo0, u5ehi3]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h143, hlam, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h4, hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h139, hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h142, hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [hlam, p147_0]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h145, hlam, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h136, h3, hc12, hc45, hlam, hphi, ht23, ht34, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                rcases p147_3 (m.d 0 5) (by simp) with h169 | h169
                                · linarith only [h169, h5, hlam]
                                · linarith only [h169, h2, hlam]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [h136, hc12, hc45, hlam, hphi, ht23, ht34, p147_1]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                rcases p147_3 (m.d 0 5) (by simp) with h173 | h173
                                · linarith only [h173, h5, hlam]
                                · linarith only [h173, h4, hlam]
                              · obtain ⟨p147_0, p147_1, p147_2, p147_3⟩ := h147c
                                linarith only [hlam, p147_0]
                        · linarith only [h139, h142, hc23, hlam, hphi, u3elo1]
                    · linarith only [h138, h139, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                    · linarith only [h138, h179, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h179, h4, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h182 | h182
            · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
              · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                    · linarith only [h186, h4, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                      · linarith only [h1, h185, h188, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                        · linarith only [h190, h4, hc03, hlam, hphi, u3elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                          · linarith only [h184, h188, h192, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                            · linarith only [h1, h184, h185, h188, h194, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                            · linarith only [h182, h194, h4, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                    · linarith only [h185, h197, h4, hc03, hlam, hphi, u3elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                        · linarith only [h200, h4, hc03, hlam, hphi, u3elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                            · rcases h5bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h184, h202, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h202, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h4, hlam, p204_1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h2, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h2, h202, hc01, hlam, hphi, ht0b, ht5b, p204_1, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h197, hlam, p204_1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h0, h184, hc01, hlam, hphi, ht0b, ht5b, p204_1, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h3, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h184, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h200, hlam, p204_1]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p204_1, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4, u5ehi0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h184, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4, u5ehi2]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo4, u5ehi2]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h203, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1, u3elo3, u5ehi4]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h182, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h199, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h202, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [h203, hlam, p204_0]
                              · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                linarith only [hlam, p204_0]
                            · linarith only [h183, h184, h185, h2, h202, h203, h4, hc23, hlam, hphi, u3elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                            · rcases h5bigk with h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h231, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo3, u5ehi1]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h231, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo3, u5ehi2]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h4, hlam, p232_1]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h202, h231, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p232_1, u3elo3]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h2, hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p232_1, u5ehi2]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h197, hlam, p232_1]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h2, h202, h231, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p232_1, u3elo3]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h3, hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h184, hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h200, hlam, p232_1]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h202, hlam, p232_1]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h231, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo3, u5ehi0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h184, h231, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo3, u5ehi2]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h231, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1, u3elo3, u5ehi2]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h202, h231, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p232_1, u3elo3]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h182, hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h199, hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h199, h2, hc01, hlam, hphi, ht0b, ht5b, p232_1, u5ehi2]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [h231, hlam, p232_0]
                              · obtain ⟨p232_0, p232_1, p232_2, p232_3⟩ := h232c
                                linarith only [hlam, p232_0]
                            · linarith only [h185, h199, h231, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                        · linarith only [h183, h259, h4, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h261 | h261
                          · linarith only [h184, h199, h261, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h263 | h263
                            · linarith only [h183, h185, h199, h263, hc23, hlam, hphi, u3elo3]
                            · linarith only [h182, h183, h185, h263, h4, hc23, hlam, hphi, u3elo4]
                · linarith only [h183, h184, h3, h4, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                · linarith only [h183, h267, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h270 | h270
                    · linarith only [h1, h270, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                      · linarith only [h1, h269, h272, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h274 | h274
                        · linarith only [h274, h4, hc03, hlam, hphi, u3elo2]
                        · linarith only [h183, h274, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
                    · linarith only [h269, h277, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                        · linarith only [h280, h4, hc03, hlam, hphi, u3elo2]
                        · linarith only [h183, h280, hc12, hlam, hphi, ht23, u3elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                        · linarith only [h283, h4, hc03, hlam, hphi, u3elo2]
                        · linarith only [h183, h283, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
              · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                    · linarith only [h1, h289, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h291 | h291
                      · linarith only [h1, h182, h288, h291, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                        · linarith only [h293, h4, hc03, hlam, hphi, u3elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                          · linarith only [h182, h295, h3, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h297 | h297
                            · linarith only [h1, h182, h2, h287, h288, h297, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                            · rcases h5bigk with h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h287, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p299_1, u3elo4, u5ehi2]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p299_1, u3elo4, u5ehi2]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h4, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h182, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h2, hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p299_1, u5ehi2]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h289, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h291, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h3, hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h287, hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h293, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h295, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p299_1, u3elo4, u5ehi0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h287, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p299_1, u3elo4, u5ehi2]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p299_1, u3elo4, u5ehi2]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, p299_0]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h297, hlam, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h1, h288, h4, hc34, hc45, hlam, hphi, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h288, h289, hc34, hc45, hlam, hphi, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                rcases p299_3 (m.d 0 5) (by simp) with h322 | h322
                                · linarith only [h182, h322, hlam]
                                · linarith only [h3, h322, hlam]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [h1, h288, h4, hc34, hc45, hlam, hphi, p299_1]
                              · obtain ⟨p299_0, p299_1, p299_2, p299_3⟩ := h299c
                                linarith only [hlam, p299_0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
                    · linarith only [h1, h327, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h329 | h329
                      · linarith only [h182, h2, h329, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                        · linarith only [h1, h286, h331, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                          · linarith only [h182, h2, h287, h333, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                            · linarith only [h286, h288, h329, h335, hc23, hlam, hphi, u3elo3]
                            · rcases h5bigk with h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c | h337c
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h287, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p337_1, u3elo4, u5ehi2]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p337_1, u3elo4, u5ehi2]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h4, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h182, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h2, hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p337_1, u5ehi2]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h327, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h329, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h3, hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h287, hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h331, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h333, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p337_1, u3elo4, u5ehi0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h287, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p337_1, u3elo4, u5ehi2]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p337_1, u3elo4, u5ehi2]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, p337_0]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h335, hlam, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                rcases p337_3 (m.d 0 5) (by simp) with h358 | h358
                                · linarith only [h182, h358, hlam]
                                · rcases p337_3 (m.d 1 5) (by simp) with h360 | h360
                                  · linarith only [h329, h360, hlam]
                                  · rcases p337_3 (m.d 2 5) (by simp) with h362 | h362
                                    · linarith only [h333, h362, hlam]
                                    · rcases p337_3 (m.d 3 5) (by simp) with h364 | h364
                                      · linarith only [h335, h364, hlam]
                                      · linarith only [h364, h4, hlam]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                rcases p337_3 (m.d 0 5) (by simp) with h367 | h367
                                · linarith only [h182, h367, hlam]
                                · linarith only [h2, h367, hlam]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                rcases p337_3 (m.d 0 5) (by simp) with h370 | h370
                                · linarith only [h182, h370, hlam]
                                · linarith only [h3, h370, hlam]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [h1, h286, h4, hc23, hc45, hlam, hphi, ht34, p337_1]
                              · obtain ⟨p337_0, p337_1, p337_2, p337_3⟩ := h337c
                                linarith only [hlam, p337_0]
                · linarith only [h286, h287, h3, h4, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h376 | h376
                · linarith only [h1, h286, h376, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
                    · linarith only [h1, h379, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                      · linarith only [h1, h182, h378, h381, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h383 | h383
                        · linarith only [h383, h4, hc03, hlam, hphi, u3elo2]
                        · linarith only [h286, h383, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                    · linarith only [h378, h386, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h388 | h388
                      · linarith only [h182, h3, h376, h378, h388, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h390 | h390
                        · linarith only [h390, h4, hc03, hlam, hphi, u3elo2]
                        · linarith only [h286, h390, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
          · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
            · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
              · rcases m.htr 1 2 5 (by decide) (by decide) with h396 | h396
                · linarith only [h0, h3, h396, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                    · linarith only [h395, h396, h399, hlam]
                    · linarith only [h393, h399, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
                    · linarith only [h398, h402, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h393, h402, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                · linarith only [h3, h395, h405, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h412 | h412
                            · linarith only [h1, h407, h412, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                            · rcases h5bigk with h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h3, h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi1]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h3, hlam, p414_1]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h3, h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi3]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h3, h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi4]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h2, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h405, hlam, p414_1]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p414_1, u5ehi3]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h2, h3, h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi4]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi1]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi3]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h410, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p414_1, u3elo2, u5ehi4]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h393, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h408, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h410, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h412, hlam, p414_1]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h394, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h409, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h411, hlam, p414_0]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [h394, hc04, hlam, hphi, ht0b, ht5b, p414_1, u5ehi3]
                              · obtain ⟨p414_0, p414_1, p414_2, p414_3⟩ := h414c
                                linarith only [hlam, p414_0]
                          · linarith only [h0, h1, h3, h407, h409, h411, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h393, h410, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h443 | h443
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
                            · linarith only [h1, h407, h409, h444, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases h5bigk with h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h393, h408, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo0, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h3, hlam, p446_1]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h393, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo0, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h393, h408, h409, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo0, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h2, hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h405, hlam, p446_1]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h409, h443, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p446_1, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h409, hlam, p446_1]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo2, u5ehi0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo2, u5ehi1]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo2, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h408, h409, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo2, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h393, hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h408, hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h442, hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h444, hlam, p446_1]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h394, hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h3, h394, h408, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo2, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h443, hlam, p446_0]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [h3, h394, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p446_1, u3elo2, u5ehi3]
                              · obtain ⟨p446_0, p446_1, p446_2, p446_3⟩ := h446c
                                linarith only [hlam, p446_0]
                          · linarith only [h3, h394, h443, hlam]
                        · linarith only [h393, h442, hc23, hlam, hphi, u3elo0]
                    · linarith only [h393, h408, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                    · linarith only [h407, h475, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h393, h475, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
              · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                · linarith only [h0, h3, h479, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                    · linarith only [h478, h479, h482, hlam]
                    · linarith only [h393, h482, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
                    · linarith only [h481, h485, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h393, h485, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
                · linarith only [h3, h478, h488, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                      · linarith only [h2, h394, h492, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h490, h492, h496, hlam]
                            · rcases h5bigk with h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h394, h495, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p498_1, u5ehi1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h3, hlam, p498_1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h393, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo0, u5ehi3]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h394, hlam, p498_1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h2, hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h488, hlam, p498_1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p498_1, u5ehi3]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h492, hlam, p498_1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo2, u5ehi0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo2, u5ehi1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo2, u5ehi3]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo2, u5ehi4]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h393, hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h491, hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h494, hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h496, hlam, p498_1]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h2, h491, h495, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p498_1, u5ehi3]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h491, h495, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p498_1, u5ehi3]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h495, hlam, p498_0]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [h494, h495, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo2, u5ehi3]
                              · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                                linarith only [hlam, p498_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                            · linarith only [h0, h3, h495, h524, hc12, hlam, hphi, ht23, u3elo3]
                            · rcases h5bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h393, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo0, u5ehi1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h3, hlam, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h393, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo0, u5ehi3]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h394, hlam, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h2, hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h488, hlam, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p526_1, u5ehi3]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h492, hlam, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo2, u5ehi0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo2, u5ehi1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p526_1, u3elo2, u5ehi3]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h495, hlam, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h393, hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h491, hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h494, hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [hlam, p526_0]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h524, hlam, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                rcases p526_3 (m.d 0 5) (by simp) with h547 | h547
                                · linarith only [h394, h547, hlam]
                                · rcases p526_3 (m.d 1 5) (by simp) with h549 | h549
                                  · linarith only [h492, h549, hlam]
                                  · rcases p526_3 (m.d 2 5) (by simp) with h551 | h551
                                    · linarith only [h495, h551, hlam]
                                    · linarith only [h3, h551, hlam]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                rcases p526_3 (m.d 0 5) (by simp) with h554 | h554
                                · linarith only [h394, h554, hlam]
                                · linarith only [h2, h554, hlam]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [h0, h3, hc12, hc45, hlam, hphi, ht23, ht34, p526_1]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                rcases p526_3 (m.d 0 5) (by simp) with h558 | h558
                                · linarith only [h394, h558, hlam]
                                · linarith only [h393, h558, hlam]
                              · obtain ⟨p526_0, p526_1, p526_2, p526_3⟩ := h526c
                                linarith only [hlam, p526_0]
                        · linarith only [h393, h494, hc23, hlam, hphi, u3elo0]
                    · linarith only [h393, h491, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h564 | h564
                    · linarith only [h490, h564, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h393, h564, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h567 | h567
            · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
              · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                · linarith only [h0, h3, h569, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                    · linarith only [h1, h393, h572, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                      · linarith only [h1, h393, h571, h574, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                        · linarith only [h393, h567, h568, h569, h574, h576, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h568, h576, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                    · linarith only [h393, h571, h579, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h581 | h581
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h582 | h582
                        · linarith only [h0, h1, h3, h393, h568, h582, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h568, h582, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                        · linarith only [h0, h3, h568, h585, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h3, h568, h585, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h588 | h588
                · linarith only [h1, h3, h568, h588, hc02, hlam, hphi, ht23, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                    · linarith only [h1, h393, h591, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                      · linarith only [h1, h393, h590, h593, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h595 | h595
                        · linarith only [h393, h595, hc03, hlam, hphi, u3elo2]
                        · linarith only [h568, h595, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
                    · linarith only [h1, h393, h598, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h600 | h600
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                        · linarith only [h393, h601, hc03, hlam, hphi, u3elo2]
                        · linarith only [h568, h601, hc12, hlam, hphi, ht23, u3elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h604 | h604
                        · linarith only [h1, h393, h568, h604, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h568, h604, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
              · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                · linarith only [h0, h3, h608, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                    · linarith only [h1, h393, h611, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
                      · linarith only [h1, h393, h567, h610, h613, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                        · linarith only [h0, h1, h3, h393, h607, h615, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h607, h615, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h618 | h618
                    · linarith only [h393, h610, h618, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
                      · linarith only [h2, h567, h607, h608, h610, h620, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h622 | h622
                        · linarith only [h0, h1, h3, h393, h607, h622, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h607, h622, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                · linarith only [h3, h607, h625, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h628 | h628
                    · linarith only [h1, h393, h628, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                      · linarith only [h1, h393, h567, h627, h630, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h632 | h632
                        · linarith only [h1, h393, h627, h632, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h607, h632, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                    · linarith only [h627, h635, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h637 | h637
                      · linarith only [h2, h567, h637, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h639 | h639
                        · linarith only [h393, h639, hc03, hlam, hphi, u3elo2]
                        · linarith only [h607, h639, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h642 | h642
        · linarith only [h0, h2, h642, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
          · linarith only [h1, h2, h644, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h646 | h646
            · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
              · linarith only [h0, h2, h644, h647, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h649 | h649
                · linarith only [h1, h2, h644, h647, h649, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h652 | h652
                    · linarith only [h1, h2, h644, h652, hlam]
                    · linarith only [h1, h2, h647, h652, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h655 | h655
                    · linarith only [h1, h2, h644, h655, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1, h2, h647, h655, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
              · linarith only [h0, h2, h644, h658, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                · linarith only [h658, h660, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h663 | h663
                    · linarith only [h1, h2, h644, h663, hlam]
                    · linarith only [h1, h2, h658, h663, hc12, hlam, hphi, ht23, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                    · linarith only [h1, h2, h666, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h1, h2, h658, h666, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h670 | h670
    · rcases m.htr 0 1 5 (by decide) (by decide) with h671 | h671
      · rcases m.htr 0 2 5 (by decide) (by decide) with h672 | h672
        · rcases m.htr 0 3 5 (by decide) (by decide) with h673 | h673
          · rcases m.htr 0 4 5 (by decide) (by decide) with h674 | h674
            · rcases m.htr 1 2 3 (by decide) (by decide) with h675 | h675
              · rcases m.htr 1 2 5 (by decide) (by decide) with h676 | h676
                · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                    · linarith only [h0, h670, h678, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h673, h678, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
                    · linarith only [h677, h681, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h673, h681, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h671, h676, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h671, h675, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
              · rcases m.htr 1 2 5 (by decide) (by decide) with h687 | h687
                · rcases m.htr 1 3 4 (by decide) (by decide) with h688 | h688
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h689 | h689
                    · linarith only [h0, h670, h689, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h673, h686, h689, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h692 | h692
                    · linarith only [h688, h692, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                    · linarith only [h673, h692, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h671, h687, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h671, h686, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h697 | h697
            · rcases m.htr 1 2 3 (by decide) (by decide) with h698 | h698
              · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
                · rcases m.htr 1 3 4 (by decide) (by decide) with h700 | h700
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h701 | h701
                    · linarith only [h670, h673, h701, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h703 | h703
                      · linarith only [h670, h673, h700, h703, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h705 | h705
                        · linarith only [h670, h673, h698, h705, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                          · linarith only [h699, h703, h707, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                            · linarith only [h700, h701, h703, h709, hlam]
                            · linarith only [h673, h697, h709, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h712 | h712
                    · linarith only [h670, h673, h712, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h714 | h714
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                        · linarith only [h670, h673, h698, h715, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h717 | h717
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h718 | h718
                            · rcases h5bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h673, h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi1]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h673, h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi2]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h673, hlam, p719_1]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h673, h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi4]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h671, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p719_1, u5ehi2]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h712, hlam, p719_1]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p719_1, u5ehi4]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h672, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h699, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h715, hlam, p719_1]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h0, h672, hc12, hlam, hphi, ht01, ht0b, ht5b, p719_1, u5ehi4]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h699, h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi2]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi2]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h718, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p719_1, u3elo3, u5ehi4]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h697, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h714, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h717, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [h718, hlam, p719_0]
                              · obtain ⟨p719_0, p719_1, p719_2, p719_3⟩ := h719c
                                linarith only [hlam, p719_0]
                            · linarith only [h0, h671, h698, h699, h700, h717, h718, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                            · rcases h5bigk with h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h673, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p747_1, u3elo4, u5ehi1]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h673, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p747_1, u3elo4, u5ehi2]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h673, hlam, p747_1]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h673, h717, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p747_1, u3elo4]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h671, hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p747_1, u5ehi2]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h712, hlam, p747_1]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h0, h671, h717, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p747_1]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h672, hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h699, hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h715, hlam, p747_1]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h717, hlam, p747_1]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p747_1, u3elo4, u5ehi0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h699, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p747_1, u3elo4, u5ehi2]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p747_1, u3elo4, u5ehi2]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h717, h746, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p747_1, u3elo3]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h697, hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h714, hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h697, hc04, hlam, hphi, ht0b, ht5b, p747_1, u5ehi2]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [h746, hlam, p747_0]
                              · obtain ⟨p747_0, p747_1, p747_2, p747_3⟩ := h747c
                                linarith only [hlam, p747_0]
                            · linarith only [h700, h714, h746, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h774 | h774
                        · linarith only [h0, h670, h698, h774, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h776 | h776
                          · linarith only [h699, h714, h776, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h778 | h778
                            · linarith only [h698, h700, h714, h778, hc23, hlam, hphi, u3elo3]
                            · linarith only [h673, h697, h698, h700, h778, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h671, h699, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h671, h698, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
              · rcases m.htr 1 2 5 (by decide) (by decide) with h784 | h784
                · rcases m.htr 1 3 4 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h786 | h786
                    · linarith only [h0, h670, h786, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
                      · linarith only [h670, h673, h697, h785, h788, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h790 | h790
                        · linarith only [h670, h673, h783, h790, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h792 | h792
                          · linarith only [h672, h697, h792, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h794 | h794
                            · linarith only [h670, h673, h697, h785, h794, hlam]
                            · rcases h5bigk with h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h0, h671, h784, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi2]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi2]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h673, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h697, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h671, hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p796_1, u5ehi2]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h786, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h788, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h672, hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h784, hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h790, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h792, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo4, u5ehi0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h784, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo4, u5ehi2]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p796_1, u3elo4, u5ehi2]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, p796_0]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h794, hlam, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h670, h673, h785, hc34, hc45, hlam, hphi, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h785, h786, hc34, hc45, hlam, hphi, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                rcases p796_3 (m.d 0 5) (by simp) with h819 | h819
                                · linarith only [h697, h819, hlam]
                                · linarith only [h672, h819, hlam]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [h670, h673, h785, hc34, hc45, hlam, hphi, p796_1]
                              · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                linarith only [hlam, p796_0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h824 | h824
                    · linarith only [h670, h673, h824, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
                      · linarith only [h671, h697, h826, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h828 | h828
                        · linarith only [h673, h783, h785, h826, h828, hc03, hc45, hlam, hphi, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h830 | h830
                          · linarith only [h671, h697, h784, h830, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
                            · linarith only [h785, h826, h832, hc13, hlam, hphi, u3elo3]
                            · rcases h5bigk with h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p834_1, u5ehi1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p834_1, u5ehi2]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h673, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h697, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h671, hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h0, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p834_1, u5ehi2]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h824, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h826, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h672, hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h784, hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h828, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h830, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p834_1, u3elo4, u5ehi0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h784, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p834_1, u3elo4, u5ehi2]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p834_1, u3elo4, u5ehi2]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, p834_0]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h832, hlam, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                rcases p834_3 (m.d 0 5) (by simp) with h855 | h855
                                · linarith only [h697, h855, hlam]
                                · rcases p834_3 (m.d 1 5) (by simp) with h857 | h857
                                  · linarith only [h826, h857, hlam]
                                  · rcases p834_3 (m.d 2 5) (by simp) with h859 | h859
                                    · linarith only [h830, h859, hlam]
                                    · rcases p834_3 (m.d 3 5) (by simp) with h861 | h861
                                      · linarith only [h832, h861, hlam]
                                      · linarith only [h673, h861, hlam]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                rcases p834_3 (m.d 0 5) (by simp) with h864 | h864
                                · linarith only [h697, h864, hlam]
                                · linarith only [h671, h864, hlam]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                rcases p834_3 (m.d 0 5) (by simp) with h867 | h867
                                · linarith only [h697, h867, hlam]
                                · linarith only [h672, h867, hlam]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [h673, hc03, hc45, hlam, hphi, ht34, p834_1]
                              · obtain ⟨p834_0, p834_1, p834_2, p834_3⟩ := h834c
                                linarith only [hlam, p834_0]
                · linarith only [h0, h671, h784, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h671, h783, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · linarith only [h0, h671, h672, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h875 | h875
        · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
          · linarith only [h670, h671, h876, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h878 | h878
            · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
              · rcases m.htr 1 2 5 (by decide) (by decide) with h880 | h880
                · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
                    · linarith only [h876, h882, hc03, hlam, hphi, u3elo1]
                    · linarith only [h670, h671, h882, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h885 | h885
                    · linarith only [h670, h671, h876, h885, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · linarith only [h670, h671, h885, hc13, hlam, hphi, u3elo4]
                · linarith only [h0, h670, h875, h879, h880, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h879, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h890 | h890
              · rcases m.htr 1 2 5 (by decide) (by decide) with h891 | h891
                · rcases m.htr 1 3 4 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h893 | h893
                    · linarith only [h670, h671, h876, h891, h893, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · linarith only [h670, h671, h893, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h896 | h896
                    · linarith only [h670, h671, h876, h896, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h670, h671, h890, h896, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h670, h875, h878, h890, h891, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h890, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h901 | h901
          · linarith only [h0, h670, h875, h901, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h903 | h903
            · rcases m.htr 1 2 3 (by decide) (by decide) with h904 | h904
              · rcases m.htr 1 2 5 (by decide) (by decide) with h905 | h905
                · rcases m.htr 1 3 4 (by decide) (by decide) with h906 | h906
                  · linarith only [h0, h670, h875, h905, h906, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h908 | h908
                    · linarith only [h0, h670, h875, h901, h908, hlam]
                    · linarith only [h0, h670, h875, h904, h905, h908, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h911 | h911
                  · linarith only [h0, h670, h905, h911, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h913 | h913
                    · linarith only [h0, h670, h875, h901, h905, h913, hc02, hc25, hlam, hphi]
                    · linarith only [h670, h671, h913, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h670, h904, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h917 | h917
              · rcases m.htr 1 2 5 (by decide) (by decide) with h918 | h918
                · rcases m.htr 1 3 4 (by decide) (by decide) with h919 | h919
                  · linarith only [h0, h670, h875, h918, h919, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h921 | h921
                    · linarith only [h0, h670, h875, h918, h921, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h670, h875, h917, h918, h921, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h924 | h924
                  · linarith only [h0, h670, h918, h924, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h926 | h926
                    · linarith only [h0, h670, h918, h926, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h670, h671, h917, h926, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h917, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h930 | h930
      · linarith only [h670, h930, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h932 | h932
        · rcases m.htr 0 3 5 (by decide) (by decide) with h933 | h933
          · rcases m.htr 0 4 5 (by decide) (by decide) with h934 | h934
            · rcases m.htr 1 2 3 (by decide) (by decide) with h935 | h935
              · rcases m.htr 1 2 5 (by decide) (by decide) with h936 | h936
                · rcases m.htr 1 3 4 (by decide) (by decide) with h937 | h937
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h938 | h938
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h939 | h939
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h941 | h941
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h942 | h942
                            · linarith only [h937, h942, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                            · rcases h5bigk with h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h930, hlam, p944_1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h930, h937, h939, h941, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p944_1, u3elo1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h930, h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p944_1, u3elo1, u5ehi3]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h930, h937, h939, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p944_1, u3elo1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p944_1, u3elo1, u5ehi0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h937, h939, h941, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p944_1, u3elo1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p944_1, u3elo1, u5ehi3]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h937, h939, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p944_1, u3elo1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h932, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h936, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h932, hc02, hlam, hphi, ht0b, ht5b, p944_1, u5ehi3]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h930, h932, h937, h939, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p944_1, u3elo1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h933, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h938, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h940, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h942, hlam, p944_1]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h934, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h939, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h941, hlam, p944_0]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [h934, hc04, hlam, hphi, ht0b, ht5b, p944_1, u5ehi3]
                              · obtain ⟨p944_0, p944_1, p944_2, p944_3⟩ := h944c
                                linarith only [hlam, p944_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                            · linarith only [h937, h941, h970, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases h5bigk with h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h930, hlam, p972_1]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h930, h937, h939, h940, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h930, h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h930, h937, h939, h940, h941, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h937, h939, h940, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h937, h939, h940, h941, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h932, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h936, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h934, h941, hc04, hlam, hphi, ht0b, ht5b, p972_1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h941, hlam, p972_1]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h933, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h938, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h940, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h970, hlam, p972_1]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h934, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h939, hlam, p972_0]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h934, hc04, hlam, hphi, ht0b, ht5b, p972_1, u5ehi2]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [h937, h939, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p972_1, u3elo1, u5ehi3]
                              · obtain ⟨p972_0, p972_1, p972_2, p972_3⟩ := h972c
                                linarith only [hlam, p972_0]
                        · linarith only [h933, h940, hc23, hlam, hphi, u3elo0]
                      · linarith only [h930, h934, h939, hlam]
                    · linarith only [h670, h933, h938, hlam]
                  · linarith only [h670, h933, h937, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h0, h932, h936, hlam]
              · linarith only [h0, h932, h935, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1005 | h1005
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1006 | h1006
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1007 | h1007
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1008 | h1008
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1009 | h1009
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1010 | h1010
                          · linarith only [h1010, h932, h934, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1012 | h1012
                            · linarith only [h1006, h1009, h1012, h932, h934, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                            · rcases h5bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h930, hlam, p1014_1]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1008, h1009, h934, hc14, hlam, hphi, ht01, ht0b, ht5b, p1014_1, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h933, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo0, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h934, hlam, p1014_1]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1007, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo1, u5ehi0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1007, h1009, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo1, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1007, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo1, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1006, h1008, h1010, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1, u3elo1]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h932, hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1005, hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h932, hc02, hlam, hphi, ht0b, ht5b, p1014_1, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1010, hlam, p1014_1]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h933, hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1007, hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1009, hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1012, hlam, p1014_1]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1006, h1008, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo1, u5ehi0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1008, hlam, p1014_0]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1006, h1008, h1009, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo1, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [h1006, h1008, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1014_1, u3elo1, u5ehi3]
                              · obtain ⟨p1014_0, p1014_1, p1014_2, p1014_3⟩ := h1014c
                                linarith only [hlam, p1014_0]
                        · linarith only [h1009, h933, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1041 | h1041
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1042 | h1042
                          · linarith only [h1042, h932, h934, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1044 | h1044
                            · linarith only [h1008, h1044, h930, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · rcases h5bigk with h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h930, hlam, p1046_1]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1041, h670, h933, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1046_1, u3elo1, u5ehi3]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h670, h933, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1046_1, u3elo1, u5ehi3]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h934, hlam, p1046_1]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1007, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1046_1, u3elo1, u5ehi0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1007, h1041, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1046_1, u3elo1, u5ehi3]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1007, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1046_1, u3elo1, u5ehi3]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1008, hlam, p1046_1]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h932, hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1005, hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1007, h930, h932, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1046_1, u3elo1, u5ehi3]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1042, hlam, p1046_1]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h933, hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1007, hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1041, hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [hlam, p1046_0]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h1044, hlam, p1046_1]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                rcases p1046_3 (m.d 0 5) (by simp) with h1067 | h1067
                                · linarith only [h1067, h934, hlam]
                                · rcases p1046_3 (m.d 1 5) (by simp) with h1069 | h1069
                                  · linarith only [h1008, h1069, hlam]
                                  · linarith only [h1069, h930, hlam]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [h930, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1046_1]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                rcases p1046_3 (m.d 0 5) (by simp) with h1073 | h1073
                                · linarith only [h1073, h934, hlam]
                                · linarith only [h1073, h932, hlam]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                rcases p1046_3 (m.d 0 5) (by simp) with h1076 | h1076
                                · linarith only [h1076, h934, hlam]
                                · linarith only [h1076, h933, hlam]
                              · obtain ⟨p1046_0, p1046_1, p1046_2, p1046_3⟩ := h1046c
                                linarith only [hlam, p1046_0]
                        · linarith only [h1041, h670, h933, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1007, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1006, h670, h933, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h0, h1005, h932, hlam]
              · linarith only [h0, h1004, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1085 | h1085
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1086 | h1086
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1087 | h1087
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1088 | h1088
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
                    · linarith only [h1089, h933, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1089, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1088, h670, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1087, h932, hlam]
              · linarith only [h0, h1086, h932, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1095 | h1095
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1097 | h1097
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1098 | h1098
                    · linarith only [h1098, h670, h933, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1098, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1097, h670, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1096, h932, hlam]
              · linarith only [h0, h1095, h932, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1104 | h1104
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1105 | h1105
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1106 | h1106
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1108 | h1108
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1109 | h1109
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1110 | h1110
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1111 | h1111
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
                            · linarith only [h1108, h1113, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                            · rcases h5bigk with h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h930, hlam, p1115_1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h932, hlam, p1115_1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1107, h1108, h1110, h932, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1115_1, u3elo1, u5ehi3]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1107, h1108, h1110, h1113, h932, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1115_1, u3elo1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1108, h1110, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1115_1, u3elo1, u5ehi0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1108, h1110, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1115_1, u3elo1, u5ehi2]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1108, h1110, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1115_1, u3elo1, u5ehi3]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1108, h1110, h1113, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1115_1, u3elo1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1105, h1107, h1113, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1115_1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1107, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1107, h1108, h1110, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1115_1, u3elo1, u5ehi3]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1107, h1108, h1110, h1113, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1115_1, u3elo1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1104, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1109, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1111, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1113, hlam, p1115_1]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1105, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1110, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1112, hlam, p1115_0]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [h1105, hc04, hlam, hphi, ht0b, ht5b, p1115_1, u5ehi3]
                              · obtain ⟨p1115_0, p1115_1, p1115_2, p1115_3⟩ := h1115c
                                linarith only [hlam, p1115_0]
                          · linarith only [h0, h1108, h1110, h1112, h932, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1104, h1111, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1105, h1110, h930, hlam]
                    · linarith only [h1104, h1109, h670, hlam]
                  · linarith only [h1104, h1108, h670, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1146 | h1146
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1147 | h1147
                    · linarith only [h1106, h1107, h1147, hlam]
                    · linarith only [h1147, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1104, h1146, h670, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · linarith only [h0, h1106, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1152 | h1152
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1153 | h1153
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1154 | h1154
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1155 | h1155
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1156 | h1156
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1157 | h1157
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1158 | h1158
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1159 | h1159
                            · linarith only [h1104, h1105, h1154, h1159, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
                            · rcases h5bigk with h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c | h1161c
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h930, hlam, p1161_1]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h932, hlam, p1161_1]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1105, h1156, hc14, hlam, hphi, ht01, ht0b, ht5b, p1161_1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1105, hlam, p1161_1]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1161_1, u3elo1, u5ehi0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h0, h1154, h1156, h932, hc01, hlam, hphi, ht12, ht23, p1161_1, u3elo1]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1161_1, u3elo1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1105, h1154, h1156, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1161_1, u3elo1]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1104, h1153, hc12, hlam, hphi, ht01, ht0b, ht5b, p1161_1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1153, hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1153, h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1161_1, u3elo1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1104, h1105, h1153, h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1161_1, u3elo1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1104, hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1155, hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1157, hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1159, hlam, p1161_1]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1104, h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1161_1, u3elo1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1156, hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1158, hlam, p1161_0]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [h1154, h1156, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1161_1, u3elo1, u5ehi3]
                              · obtain ⟨p1161_0, p1161_1, p1161_2, p1161_3⟩ := h1161c
                                linarith only [hlam, p1161_0]
                          · linarith only [h0, h1154, h1156, h1158, h932, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1104, h1157, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1189 | h1189
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1190 | h1190
                          · linarith only [h1153, h1156, h1190, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1192 | h1192
                            · linarith only [h0, h1153, h1156, h1192, h932, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · rcases h5bigk with h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h930, hlam, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h932, hlam, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1104, h670, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1194_1, u3elo1, u5ehi3]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1105, hlam, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1155, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1194_1, u3elo1, u5ehi0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h0, h1155, h932, hc01, hlam, hphi, ht12, ht23, p1194_1, u3elo1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1155, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1194_1, u3elo1, u5ehi3]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1156, hlam, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1104, h1153, hc12, hlam, hphi, ht01, ht0b, ht5b, p1194_1, u5ehi3]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1153, hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1153, h1155, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1194_1, u3elo1, u5ehi3]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1190, hlam, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1104, hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1155, hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1189, hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [hlam, p1194_0]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h1192, hlam, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                rcases p1194_3 (m.d 0 5) (by simp) with h1215 | h1215
                                · linarith only [h1105, h1215, hlam]
                                · rcases p1194_3 (m.d 1 5) (by simp) with h1217 | h1217
                                  · linarith only [h1156, h1217, hlam]
                                  · linarith only [h1217, h930, hlam]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h930, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [h0, h932, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1194_1]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                rcases p1194_3 (m.d 0 5) (by simp) with h1222 | h1222
                                · linarith only [h1105, h1222, hlam]
                                · linarith only [h1104, h1222, hlam]
                              · obtain ⟨p1194_0, p1194_1, p1194_2, p1194_3⟩ := h1194c
                                linarith only [hlam, p1194_0]
                        · linarith only [h1104, h1189, h670, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1104, h1155, h670, hlam]
                  · linarith only [h1104, h1154, h670, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1229 | h1229
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1230 | h1230
                    · linarith only [h1152, h1153, h1230, hlam]
                    · linarith only [h1104, h1229, h1230, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h1104, h1229, h670, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · linarith only [h0, h1152, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1235 | h1235
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1236 | h1236
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1237 | h1237
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1238 | h1238
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1239 | h1239
                    · linarith only [h1104, h1239, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1239, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1238, h670, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1244 | h1244
                    · linarith only [h1104, h1244, h670, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1244, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1243, h670, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h1236, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1250 | h1250
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1251 | h1251
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1252 | h1252
                    · linarith only [h1104, h1252, h670, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1252, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1251, h670, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1256 | h1256
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1257 | h1257
                    · linarith only [h1104, h1257, h670, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1257, h670, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1256, h670, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h1249, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem n7l_sAB3_H_I_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h4emin := hb4.2.1
  have h5elo := hb5.1
  have h3elo := hb3.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · linarith only [h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases h4emin with h10 | h10 | h10 | h10 | h10
              · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
                · rcases m.htr 0 3 4 (by decide) (by decide) with h12 | h12
                  · linarith only [h12, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h12, h6, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h11, hlam, p0_0]
              · linarith only [h10, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
                · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h18, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h18, h6, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h17, hlam, p0_0]
              · linarith only [h10, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h10, hlam, ht45, u5elo4]
        · rcases p0_3 (m.d 3 4) (by simp) with h24 | h24
          · linarith only [h24, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases h4emin with h28 | h28 | h28 | h28 | h28
              · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
                · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h30, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h24, h30, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h29, hlam, p0_0]
              · linarith only [h28, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h28, h5, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h24, h28, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h26, h28, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h39 | h39
    · rcases p0_3 (m.d 1 4) (by simp) with h40 | h40
      · rcases p0_3 (m.d 2 4) (by simp) with h41 | h41
        · linarith only [h41, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h45, hc24, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h47 | h47 | h47 | h47 | h47
              · rcases m.htr 0 1 4 (by decide) (by decide) with h48 | h48
                · linarith only [h40, h48, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
                  · linarith only [h50, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h43, h50, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h53 | h53
                · linarith only [h40, h53, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h55 | h55
                  · linarith only [h55, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h43, h55, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h40, h47, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h40, h43, h47, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h40, h45, h47, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 4) (by simp) with h61 | h61
        · linarith only [h61, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h63 | h63
          · linarith only [h40, h63, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h65 | h65
            · linarith only [h40, h65, hc14, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h67 | h67 | h67 | h67 | h67
              · rcases m.htr 0 1 4 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h40, h69, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h63, h68, h69, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h40, h68, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h40, h67, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h67, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h63, h67, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h65, h67, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
    · linarith only [h39, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h78 | h78
    · rcases p0_3 (m.d 1 4) (by simp) with h79 | h79
      · rcases p0_3 (m.d 2 4) (by simp) with h80 | h80
        · rcases p0_3 (m.d 3 4) (by simp) with h81 | h81
          · linarith only [h81, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc34, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h85 | h85 | h85 | h85 | h85
              · rcases m.htr 0 1 4 (by decide) (by decide) with h86 | h86
                · linarith only [h79, h86, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h88, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
                · linarith only [h79, h91, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h93 | h93
                  · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h93, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h96 | h96
                · linarith only [h79, h96, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h98, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h98, hlam, p0_0]
              · linarith only [h85, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h83, h85, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · linarith only [h103, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h105 | h105
            · linarith only [h105, h80, hc24, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h107 | h107 | h107 | h107 | h107
              · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                · linarith only [h108, h79, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
                  · linarith only [h110, h80, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h110, hlam, p0_0]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h113 | h113
                · linarith only [h113, h79, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
                  · linarith only [h115, h80, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h115, hlam, p0_0]
              · linarith only [h107, h80, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h107, h79, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h105, h107, h79, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 4) (by simp) with h121 | h121
        · rcases p0_3 (m.d 3 4) (by simp) with h122 | h122
          · linarith only [h122, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h124 | h124
            · linarith only [h124, h79, hc14, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h126 | h126 | h126 | h126 | h126
              · rcases m.htr 0 1 4 (by decide) (by decide) with h127 | h127
                · rcases m.htr 0 3 4 (by decide) (by decide) with h128 | h128
                  · linarith only [h128, h79, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h128, hlam, p0_0]
                · linarith only [h127, h79, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h121, h126, h79, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h133 | h133
                · rcases m.htr 0 3 4 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, h79, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h134, hlam, p0_0]
                · linarith only [h133, h79, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h121, h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h121, h124, h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h140 | h140
          · linarith only [h140, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h142 | h142
            · linarith only [h142, h79, hc14, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h144 | h144 | h144 | h144 | h144
              · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
                · rcases m.htr 0 3 4 (by decide) (by decide) with h146 | h146
                  · linarith only [h146, h79, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h146, hlam, p0_0]
                · linarith only [h145, h79, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h144, h79, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h121, h144, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h144, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h142, h144, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
    · linarith only [h78, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h155 | h155
    · rcases p0_3 (m.d 1 4) (by simp) with h156 | h156
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · rcases p0_3 (m.d 3 4) (by simp) with h158 | h158
          · linarith only [h158, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h160, hlam, p0_0]
            · rcases h4emin with h162 | h162 | h162 | h162 | h162
              · rcases m.htr 0 1 4 (by decide) (by decide) with h163 | h163
                · linarith only [h156, h163, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h165 | h165
                  · linarith only [h158, h165, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h158, h165, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
                · linarith only [h156, h168, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h170 | h170
                  · linarith only [h158, h170, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h158, h170, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h173 | h173
                · linarith only [h156, h173, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
                  · linarith only [h175, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo0]
                  · linarith only [h158, h175, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h157, h158, h162, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h157, h162, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h180 | h180
          · linarith only [h157, h180, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h182 | h182
            · linarith only [h182, hlam, p0_0]
            · rcases h4emin with h184 | h184 | h184 | h184 | h184
              · rcases m.htr 0 1 4 (by decide) (by decide) with h185 | h185
                · linarith only [h156, h185, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h187 | h187
                  · linarith only [h157, h187, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h180, h187, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h190 | h190
                · linarith only [h156, h190, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h180, h192, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h180, h192, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h156, h157, h184, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h156, h180, h184, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h156, h184, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · rcases p0_3 (m.d 2 4) (by simp) with h198 | h198
        · rcases p0_3 (m.d 3 4) (by simp) with h199 | h199
          · linarith only [h156, h199, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h201 | h201
            · linarith only [h201, hlam, p0_0]
            · rcases h4emin with h203 | h203 | h203 | h203 | h203
              · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
                · rcases m.htr 0 3 4 (by decide) (by decide) with h205 | h205
                  · linarith only [h156, h205, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h199, h204, h205, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h156, h198, h204, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h156, h198, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h210 | h210
                · rcases m.htr 0 3 4 (by decide) (by decide) with h211 | h211
                  · linarith only [h156, h211, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h199, h210, h211, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h156, h198, h210, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h198, h199, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h198, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h217 | h217
          · linarith only [h156, h217, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h219 | h219
            · linarith only [h219, hlam, p0_0]
            · rcases h4emin with h221 | h221 | h221 | h221 | h221
              · rcases m.htr 0 1 4 (by decide) (by decide) with h222 | h222
                · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
                  · linarith only [h156, h223, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h217, h222, h223, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h156, h222, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1]
              · linarith only [h156, h221, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h198, h221, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h217, h221, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h221, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
    · linarith only [h155, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h232 | h232
    · linarith only [h232, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h234 | h234
      · rcases p0_3 (m.d 2 4) (by simp) with h235 | h235
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · linarith only [h236, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h238 | h238
            · linarith only [h238, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h240 | h240 | h240 | h240 | h240
              · linarith only [h240, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h242 | h242
                · linarith only [h242, hlam, p0_0]
                · linarith only [h235, h242, hc01, hc24, hlam, hphi, ht12, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h245 | h245
                · linarith only [h245, hlam, p0_0]
                · linarith only [h235, h245, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h235, h236, h240, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h235, h238, h240, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · linarith only [h250, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h252 | h252
            · linarith only [h252, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h254 | h254 | h254 | h254 | h254
              · linarith only [h254, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h256 | h256
                · linarith only [h256, hlam, p0_0]
                · linarith only [h256, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h235, h254, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h250, h254, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h252, h254, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h234, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h264 | h264
    · rcases p0_3 (m.d 1 4) (by simp) with h265 | h265
      · rcases p0_3 (m.d 2 4) (by simp) with h266 | h266
        · linarith only [h266, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h268 | h268
          · linarith only [h268, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h270 | h270
            · linarith only [h270, hc24, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h272 | h272 | h272 | h272 | h272
              · rcases m.htr 0 1 4 (by decide) (by decide) with h273 | h273
                · linarith only [h273, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h264, h273, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h276 | h276
                · linarith only [h276, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h264, h276, hlam]
              · linarith only [h272, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h268, h272, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h270, h272, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h265, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h283 | h283
      · rcases p0_3 (m.d 2 4) (by simp) with h284 | h284
        · linarith only [h284, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h286 | h286
          · linarith only [h264, h286, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h264, h288, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h290 | h290 | h290 | h290 | h290
              · linarith only [h264, h290, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h292 | h292
                · linarith only [h264, h292, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h264, h292, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h290, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h286, h290, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h288, h290, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h283, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h299 | h299
    · rcases p0_3 (m.d 1 4) (by simp) with h300 | h300
      · rcases p0_3 (m.d 2 4) (by simp) with h301 | h301
        · rcases p0_3 (m.d 3 4) (by simp) with h302 | h302
          · linarith only [h302, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h304 | h304
            · linarith only [h304, hc34, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h306 | h306 | h306 | h306 | h306
              · rcases m.htr 0 1 4 (by decide) (by decide) with h307 | h307
                · linarith only [h307, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h307, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h310 | h310
                · linarith only [h310, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h310, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h313 | h313
                · linarith only [h313, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h313, hlam]
              · linarith only [h306, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h301, h304, h306, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h318 | h318
          · linarith only [h318, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h320 | h320
            · linarith only [h301, h320, hc24, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h322 | h322 | h322 | h322 | h322
              · rcases m.htr 0 1 4 (by decide) (by decide) with h323 | h323
                · linarith only [h301, h323, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h323, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h326 | h326
                · linarith only [h301, h326, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h326, hlam]
              · linarith only [h301, h322, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h322, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h320, h322, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h300, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h333 | h333
      · rcases p0_3 (m.d 2 4) (by simp) with h334 | h334
        · rcases p0_3 (m.d 3 4) (by simp) with h335 | h335
          · linarith only [h335, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h337 | h337
            · linarith only [h299, h337, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h339 | h339 | h339 | h339 | h339
              · linarith only [h299, h339, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h341 | h341
                · linarith only [h299, h341, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h341, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
                · linarith only [h299, h344, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h344, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h334, h339, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h334, h337, h339, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h349 | h349
          · linarith only [h349, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h351 | h351
            · linarith only [h299, h351, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h353 | h353 | h353 | h353 | h353
              · linarith only [h299, h353, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h355 | h355
                · linarith only [h299, h355, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h299, h355, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h334, h353, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h353, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h351, h353, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h333, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h362 | h362
    · rcases p0_3 (m.d 1 4) (by simp) with h363 | h363
      · rcases p0_3 (m.d 2 4) (by simp) with h364 | h364
        · rcases p0_3 (m.d 3 4) (by simp) with h365 | h365
          · linarith only [h365, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h367 | h367
            · linarith only [h367, hlam, p0_0]
            · rcases h4emin with h369 | h369 | h369 | h369 | h369
              · rcases m.htr 0 1 4 (by decide) (by decide) with h370 | h370
                · linarith only [h365, h370, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h370, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h373 | h373
                · linarith only [h365, h373, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h373, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h376 | h376
                · linarith only [h365, h376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h376, hlam]
              · linarith only [h365, h369, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h369, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h381 | h381
          · linarith only [h364, h381, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h383 | h383
            · linarith only [h383, hlam, p0_0]
            · rcases h4emin with h385 | h385 | h385 | h385 | h385
              · rcases m.htr 0 1 4 (by decide) (by decide) with h386 | h386
                · linarith only [h364, h386, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h386, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h389 | h389
                · linarith only [h364, h389, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h389, hlam]
              · linarith only [h364, h385, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h381, h385, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h385, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h363, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h396 | h396
      · rcases p0_3 (m.d 2 4) (by simp) with h397 | h397
        · rcases p0_3 (m.d 3 4) (by simp) with h398 | h398
          · linarith only [h362, h398, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h400 | h400
            · linarith only [h400, hlam, p0_0]
            · rcases h4emin with h402 | h402 | h402 | h402 | h402
              · linarith only [h362, h402, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h404 | h404
                · linarith only [h362, h404, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h404, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h407 | h407
                · linarith only [h362, h407, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h407, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h397, h398, h402, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h397, h402, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 3 4) (by simp) with h412 | h412
          · linarith only [h397, h412, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h414 | h414
            · linarith only [h414, hlam, p0_0]
            · rcases h4emin with h416 | h416 | h416 | h416 | h416
              · linarith only [h362, h416, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h418 | h418
                · linarith only [h362, h418, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h362, h418, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h397, h416, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h412, h416, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · linarith only [h416, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
      · linarith only [h396, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h425 | h425
    · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h427 | h427
      · rcases p0_3 (m.d 2 4) (by simp) with h428 | h428
        · rcases p0_3 (m.d 3 4) (by simp) with h429 | h429
          · linarith only [h429, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h431 | h431
            · linarith only [h431, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h433 | h433 | h433 | h433 | h433
              · linarith only [h433, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h435 | h435
                · linarith only [h427, h435, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h427, h435, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h438 | h438
                · linarith only [h427, h438, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h427, h438, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h429, h433, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h431, h433, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h428, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h444 | h444
        · rcases p0_3 (m.d 3 4) (by simp) with h445 | h445
          · linarith only [h445, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h447 | h447
            · linarith only [h447, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h449 | h449 | h449 | h449 | h449
              · linarith only [h449, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h427, h449, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h452 | h452
                · rcases m.htr 0 3 4 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
                    · linarith only [h454, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1]
                    · linarith only [h447, h454, hlam]
                  · linarith only [h445, h453, hlam]
                · linarith only [h427, h452, hlam]
              · linarith only [h445, h449, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h449, hlam, ht45, u5elo4]
        · linarith only [h444, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h462 | h462
    · rcases p0_3 (m.d 1 4) (by simp) with h463 | h463
      · linarith only [h463, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h465 | h465
        · rcases p0_3 (m.d 3 4) (by simp) with h466 | h466
          · linarith only [h466, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h468 | h468
            · linarith only [h468, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases h4emin with h470 | h470 | h470 | h470 | h470
              · rcases m.htr 0 1 4 (by decide) (by decide) with h471 | h471
                · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
                  · linarith only [h462, h472, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h462, h466, h471, h472, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h471, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h470, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h477 | h477
                · rcases m.htr 0 3 4 (by decide) (by decide) with h478 | h478
                  · linarith only [h462, h478, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h462, h466, h478, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h477, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h466, h470, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h468, h470, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h465, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h485 | h485
      · linarith only [h485, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h487 | h487
        · rcases p0_3 (m.d 3 4) (by simp) with h488 | h488
          · linarith only [h462, h488, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h490 | h490
            · linarith only [h490, hc14, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h492 | h492 | h492 | h492 | h492
              · linarith only [h462, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h495 | h495
                · linarith only [h462, h495, hlam]
                · linarith only [h495, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h488, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h490, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h487, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
    · rcases p0_3 (m.d 1 4) (by simp) with h503 | h503
      · rcases p0_3 (m.d 2 4) (by simp) with h504 | h504
        · rcases p0_3 (m.d 3 4) (by simp) with h505 | h505
          · linarith only [h505, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h507 | h507
            · linarith only [h507, hc34, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases h4emin with h509 | h509 | h509 | h509 | h509
              · rcases m.htr 0 1 4 (by decide) (by decide) with h510 | h510
                · linarith only [h503, h510, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h512 | h512
                  · linarith only [h502, h512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h502, h512, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h515 | h515
                · linarith only [h503, h515, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h517 | h517
                  · linarith only [h502, h517, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h502, h517, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h520 | h520
                · linarith only [h503, h520, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h522 | h522
                  · linarith only [h502, h522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h502, h522, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h509, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h507, h509, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h504, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h528 | h528
        · rcases p0_3 (m.d 3 4) (by simp) with h529 | h529
          · linarith only [h529, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h531 | h531
            · linarith only [h503, h531, hc14, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h533 | h533 | h533 | h533 | h533
              · rcases m.htr 0 1 4 (by decide) (by decide) with h534 | h534
                · rcases m.htr 0 3 4 (by decide) (by decide) with h535 | h535
                  · linarith only [h502, h503, h535, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h502, h535, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h503, h534, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h503, h533, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h540 | h540
                · rcases m.htr 0 3 4 (by decide) (by decide) with h541 | h541
                  · linarith only [h502, h503, h541, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h502, h541, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h503, h540, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h533, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h531, h533, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h528, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h548 | h548
      · rcases p0_3 (m.d 2 4) (by simp) with h549 | h549
        · rcases p0_3 (m.d 3 4) (by simp) with h550 | h550
          · linarith only [h550, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h552 | h552
            · linarith only [h502, h552, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h554 | h554 | h554 | h554 | h554
              · linarith only [h502, h548, h554, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h556 | h556
                · linarith only [h502, h548, h556, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h502, h548, h556, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h559 | h559
                · linarith only [h502, h548, h559, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h502, h548, h559, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h554, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h552, h554, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h549, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h565 | h565
        · rcases p0_3 (m.d 3 4) (by simp) with h566 | h566
          · linarith only [h566, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h568 | h568
            · linarith only [h502, h568, hc04, hc45, hlam, hphi, p0_1]
            · rcases h4emin with h570 | h570 | h570 | h570 | h570
              · linarith only [h502, h570, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h548, h570, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h573 | h573
                · rcases m.htr 0 3 4 (by decide) (by decide) with h574 | h574
                  · linarith only [h502, h574, hlam]
                  · linarith only [h574, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                · linarith only [h548, h573, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h570, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h568, h570, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h565, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 4) (by simp) with h581 | h581
    · rcases p0_3 (m.d 1 4) (by simp) with h582 | h582
      · rcases p0_3 (m.d 2 4) (by simp) with h583 | h583
        · rcases p0_3 (m.d 3 4) (by simp) with h584 | h584
          · linarith only [h584, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h586 | h586
            · linarith only [h586, hlam, p0_0]
            · rcases h4emin with h588 | h588 | h588 | h588 | h588
              · rcases m.htr 0 1 4 (by decide) (by decide) with h589 | h589
                · linarith only [h582, h584, h589, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h591 | h591
                  · linarith only [h581, h584, h591, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h581, h584, h591, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h594 | h594
                · linarith only [h582, h584, h594, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
                  · linarith only [h581, h584, h596, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h581, h584, h596, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h599 | h599
                · linarith only [h582, h584, h599, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h601 | h601
                  · linarith only [h581, h584, h601, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h581, h584, h601, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h584, h588, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h588, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h583, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h607 | h607
        · rcases p0_3 (m.d 3 4) (by simp) with h608 | h608
          · linarith only [h582, h608, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h610 | h610
            · linarith only [h610, hlam, p0_0]
            · rcases h4emin with h612 | h612 | h612 | h612 | h612
              · rcases m.htr 0 1 4 (by decide) (by decide) with h613 | h613
                · rcases m.htr 0 3 4 (by decide) (by decide) with h614 | h614
                  · linarith only [h581, h582, h614, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h581, h608, h614, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h582, h613, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h582, h612, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h619 | h619
                · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
                  · linarith only [h581, h582, h620, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo0]
                  · linarith only [h581, h608, h620, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                · linarith only [h582, h619, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h608, h612, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h612, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h607, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h627 | h627
      · rcases p0_3 (m.d 2 4) (by simp) with h628 | h628
        · rcases p0_3 (m.d 3 4) (by simp) with h629 | h629
          · linarith only [h581, h629, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h631 | h631
            · linarith only [h631, hlam, p0_0]
            · rcases h4emin with h633 | h633 | h633 | h633 | h633
              · linarith only [h581, h627, h633, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h635 | h635
                · linarith only [h581, h627, h635, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h581, h627, h635, hc01, hc14, hlam, hphi, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h638 | h638
                · linarith only [h581, h627, h638, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                · linarith only [h581, h627, h638, hc01, hc14, hlam, hphi, p0_1]
              · linarith only [h629, h633, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h633, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h628, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h644 | h644
        · rcases p0_3 (m.d 3 4) (by simp) with h645 | h645
          · linarith only [h581, h645, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
          · rcases p0_3 (m.d 4 5) (by simp) with h647 | h647
            · linarith only [h647, hlam, p0_0]
            · rcases h4emin with h649 | h649 | h649 | h649 | h649
              · linarith only [h581, h649, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h627, h649, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h652 | h652
                · rcases m.htr 0 3 4 (by decide) (by decide) with h653 | h653
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h654 | h654
                    · linarith only [h581, h654, hlam]
                    · linarith only [h654, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
                  · linarith only [h645, h653, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1]
                · linarith only [h627, h652, hc01, hc24, hlam, hphi, ht12, p0_1]
              · linarith only [h645, h649, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
              · linarith only [h649, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1]
        · linarith only [h644, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB3_M_IR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h3elo := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h3, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h3, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
                · linarith only [h3, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h2, h3, h5, h6, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · linarith only [h15, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h21, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h1, h18, h21, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h15, h18, h20, hlam]
                    · linarith only [h19, h3, h5, hc13, hlam, hphi, u3elo0]
                  · linarith only [h18, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
                · linarith only [h17, h3, h5, hc12, hlam, hphi, ht23, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h1, h31, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h28, h33, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h3, h33, hc23, hlam, hphi, u3elo0]
                · linarith only [h3, h30, hc13, hlam, hphi, u3elo0]
              · linarith only [h2, h28, h29, h4, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
              · linarith only [h28, h38, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h2, h38, h4, h41, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h2, h4, h44, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                        · linarith only [h4, h40, h46, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases h4bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h4, hc45, hlam, hphi, p48_1, u4ehi1]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h28, h38, h4, h40, hc12, hc45, hlam, hphi, ht23, p48_1, u3elo2, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h4, hc45, hlam, hphi, p48_1, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h4, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h1, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h38, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p48_1, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h41, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h2, hlam, p48_1]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p48_1, u4ehi1]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h2, h4, hc45, hlam, hphi, p48_1, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h44, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h3, hlam, p48_1]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h40, hlam, p48_1]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h43, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h46, hlam, p48_0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hc45, hlam, hphi, p48_1, u4ehi0]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h40, hc45, hlam, hphi, p48_1, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [h28, h38, h40, hc12, hc45, hlam, hphi, ht23, p48_1, u3elo2, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hc45, hlam, hphi, p48_1, u4ehi3]
                          · obtain ⟨p48_0, p48_1, p48_2, p48_3⟩ := h48c
                            linarith only [hlam, p48_0]
                    · linarith only [h28, h40, h43, hlam]
                · linarith only [h3, h40, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
          · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
            · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                · linarith only [h3, h76, h79, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                    · linarith only [h1, h3, h81, h82, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                      · linarith only [h0, h78, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h3, h81, h84, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                  · linarith only [h3, h76, h81, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
              · linarith only [h2, h3, h77, h78, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
              · linarith only [h77, h89, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                · linarith only [h3, h91, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h91, h94, hc13, hlam, hphi, u3elo2]
                    · linarith only [h77, h94, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h3, h76, h93, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
            · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
              · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h3, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                  · linarith only [h1, h102, h76, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                    · linarith only [h100, h104, h98, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                      · linarith only [h1, h106, h76, h99, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h1, h108, h76, h99, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                        · rcases h4bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h3, h99, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p110_1, u3elo3, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h108, h3, hc45, hlam, hphi, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h3, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h76, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h1, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h100, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h102, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h2, hlam, p110_1]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h99, hlam, p110_1]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h104, hlam, p110_1]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h106, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h108, hc45, hlam, hphi, p110_1, u4ehi0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h108, h99, hc45, hlam, hphi, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h108, hc45, hlam, hphi, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h108, hlam, p110_0]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h1, h99, hc45, hlam, hphi, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h99, hc45, hlam, hphi, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [hc45, hlam, hphi, p110_1, u4ehi2]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [h3, hc03, hc45, hlam, hphi, ht34, p110_1]
                          · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                            linarith only [hlam, p110_0]
              · linarith only [h2, h3, h98, h99, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
              · linarith only [h137, h98, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
                · linarith only [h139, h3, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                  · linarith only [h1, h141, h76, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h143, h3, hc03, hlam, hphi, u3elo2]
                    · linarith only [h143, h98, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h146 | h146
        · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
          · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
            · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
              · linarith only [h0, h149, h2, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                · linarith only [h148, h149, h151, hlam]
                · linarith only [h146, h151, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
              · linarith only [h148, h154, h2, hc02, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h146, h160, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h147, h158, h160, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi3]
                      · linarith only [h0, h1, h157, h159, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h146, h148, h158, hc13, hlam, hphi, u3elo0]
                  · linarith only [h146, h147, h157, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
                · linarith only [h146, h156, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
            · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
              · linarith only [h0, h168, h2, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                · linarith only [h1, h147, h167, h168, h170, hc45, hlam, hphi, u4ehi3]
                · linarith only [h146, h170, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
              · linarith only [h167, h173, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h1, h147, h176, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                      · linarith only [h147, h178, h179, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                        · linarith only [h0, h175, h179, h181, h2, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h4bigk with h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h179, h2, hc45, hlam, hphi, p183_1, u4ehi1]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h2, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h179, h2, hc45, hlam, hphi, p183_1, u4ehi3]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h147, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h1, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h173, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p183_1, u4ehi3]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h176, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h179, hc45, hlam, hphi, p183_1, u4ehi0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h179, hc45, hlam, hphi, p183_1, u4ehi1]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h179, hc45, hlam, hphi, p183_1, u4ehi3]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h179, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h146, hlam, p183_1]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h175, hlam, p183_1]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h178, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h181, hlam, p183_0]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h1, h175, hc45, hlam, hphi, p183_1, u4ehi3]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [h175, hc45, hlam, hphi, p183_1, u4ehi3]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hc45, hlam, hphi, p183_1, u4ehi2]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hc45, hlam, hphi, p183_1, u4ehi3]
                          · obtain ⟨p183_0, p183_1, p183_2, p183_3⟩ := h183c
                            linarith only [hlam, p183_0]
                    · linarith only [h167, h175, h178, hlam]
                · linarith only [h146, h175, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
          · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
            · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
              · linarith only [h0, h2, h213, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                · linarith only [h146, h211, h215, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                    · linarith only [h0, h1, h146, h212, h217, h218, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h2, h212, h218, hc23, hlam, hphi, u3elo3]
                  · linarith only [h146, h211, h217, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
              · linarith only [h2, h212, h222, hc02, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                · linarith only [h146, h224, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                    · linarith only [h146, h227, hc03, hlam, hphi, u3elo2]
                    · linarith only [h212, h227, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h146, h211, h226, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
            · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
              · linarith only [h0, h2, h232, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                · linarith only [h146, h234, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h0, h1, h2, h211, h231, h236, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                    · linarith only [h0, h2, h231, h234, h238, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h231, h238, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
              · linarith only [h0, h2, h241, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                · linarith only [h146, h243, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                  · linarith only [h1, h211, h245, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                    · linarith only [h231, h243, h247, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h231, h247, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h250 | h250
      · linarith only [h0, h1, h250, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
        · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
          · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
            · linarith only [h0, h1, h252, h254, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
              · linarith only [h0, h1, h252, h256, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
                · linarith only [h0, h1, h258, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h252, h258, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
            · linarith only [h0, h1, h252, h261, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
              · linarith only [h0, h1, h253, h263, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                · linarith only [h0, h1, h261, h265, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h252, h265, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h268 | h268
          · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
            · linarith only [h0, h1, h252, h269, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
              · linarith only [h0, h1, h252, h271, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                · linarith only [h252, h268, h273, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                · linarith only [h0, h1, h273, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
            · linarith only [h0, h1, h268, h276, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
              · linarith only [h0, h1, h268, h278, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
                · linarith only [h252, h280, hc03, hlam, hphi, u3elo1]
                · linarith only [h0, h1, h280, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h283 | h283
    · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
      · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
        · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
          · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
            · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
              · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h0, h283, h290, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h285, h286, h290, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
                · linarith only [h285, h289, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h283, h288, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h283, h287, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
            · rcases m.htr 1 2 4 (by decide) (by decide) with h297 | h297
              · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                · rcases m.htr 1 4 5 (by decide) (by decide) with h299 | h299
                  · linarith only [h283, h286, h299, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h302 | h302
                      · linarith only [h283, h286, h297, h302, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                        · linarith only [h283, h286, h297, h301, h304, hlam]
                        · rcases h4bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h286, h297, h301, hc45, hlam, hphi, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h286, h301, hc45, hlam, hphi, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h286, hc45, hlam, hphi, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h286, hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h283, hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h0, h283, h301, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h0, h283, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h299, hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h284, hlam, p306_1]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h297, hlam, p306_1]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h0, h284, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h302, hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h285, hlam, p306_1]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h298, hlam, p306_1]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h301, hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h304, hlam, p306_0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hc45, hlam, hphi, p306_1, u4ehi0]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h297, hc45, hlam, hphi, p306_1, u4ehi2]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [h301, hc45, hlam, hphi, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hc45, hlam, hphi, p306_1, u4ehi3]
                          · obtain ⟨p306_0, p306_1, p306_2, p306_3⟩ := h306c
                            linarith only [hlam, p306_0]
                    · linarith only [h285, h301, hc23, hlam, hphi, u3elo0]
                · linarith only [h285, h298, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h283, h297, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h283, h296, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h336 | h336
          · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
            · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
              · rcases m.htr 1 3 4 (by decide) (by decide) with h339 | h339
                · linarith only [h285, h336, h339, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                  · linarith only [h0, h283, h341, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h285, h336, h341, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
              · linarith only [h0, h283, h338, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h283, h336, h337, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
            · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
              · rcases m.htr 1 3 4 (by decide) (by decide) with h348 | h348
                · linarith only [h285, h348, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
                  · linarith only [h283, h336, h350, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                    · linarith only [h0, h283, h346, h348, h352, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                      · linarith only [h0, h283, h336, h347, h354, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                        · linarith only [h283, h336, h347, h356, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                        · rcases h4bigk with h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h285, h347, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p358_1, u3elo3, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h285, h356, hc45, hlam, hphi, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h285, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h336, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h283, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h0, h283, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h348, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h350, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h284, hlam, p358_1]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h347, hlam, p358_1]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h352, hlam, p358_1]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h354, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h356, hc45, hlam, hphi, p358_1, u4ehi0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h347, h356, hc45, hlam, hphi, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h356, hc45, hlam, hphi, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h356, hlam, p358_0]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h283, h347, hc45, hlam, hphi, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h347, hc45, hlam, hphi, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [hc45, hlam, hphi, p358_1, u4ehi2]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [h285, hc03, hc45, hlam, hphi, ht34, p358_1]
                          · obtain ⟨p358_0, p358_1, p358_2, p358_3⟩ := h358c
                            linarith only [hlam, p358_0]
              · linarith only [h0, h283, h347, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h283, h346, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h283, h284, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h387 | h387
      · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
        · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
          · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
            · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
              · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h396 | h396
                        · linarith only [h388, h396, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h387, h395, h396, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h283, h389, h392, h395, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi2]
                    · linarith only [h388, h394, hc23, hlam, hphi, u3elo0]
                  · linarith only [h283, h389, h393, hlam]
                · linarith only [h388, h392, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h387, h391, hlam]
            · linarith only [h0, h390, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
            · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
              · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                  · linarith only [h389, h407, h408, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                      · linarith only [h387, h408, h411, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                        · linarith only [h283, h405, h408, h410, h413, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi0]
                        · rcases h4bigk with h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h283, hlam, p415_1]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h283, h408, h410, hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h283, h408, hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h389, hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h408, hc45, hlam, hphi, p415_1, u4ehi0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h408, h410, hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h408, hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h408, hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h387, hlam, p415_1]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h406, hlam, p415_1]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h283, h387, h408, hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h411, hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h388, hlam, p415_1]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h407, hlam, p415_1]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h410, hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h413, hlam, p415_0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hc45, hlam, hphi, p415_1, u4ehi0]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hc45, hlam, hphi, p415_1, u4ehi1]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [h410, hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hc45, hlam, hphi, p415_1, u4ehi3]
                          · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                            linarith only [hlam, p415_0]
                    · linarith only [h388, h410, hc23, hlam, hphi, u3elo0]
                · linarith only [h388, h407, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h387, h406, hlam]
            · linarith only [h0, h405, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
          · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
            · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
              · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                · linarith only [h388, h445, h448, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                    · linarith only [h446, h448, h451, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                        · rcases h4bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h283, hlam, p455_1]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h453, hc04, hlam, hphi, ht0b, ht45, ht5b, p455_1, u4ehi4]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h388, hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h283, h448, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi4]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h448, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h448, h453, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi4]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h448, hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h448, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi4]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h387, hlam, p455_1]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h447, hlam, p455_1]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h451, hlam, p455_1]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h387, hc02, hlam, hphi, ht0b, ht45, ht5b, p455_1, u4ehi4]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi1]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi2]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p455_1, u3elo3, u4ehi4]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h445, hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h450, hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h453, hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [h454, hlam, p455_0]
                          · obtain ⟨p455_0, p455_1, p455_2, p455_3⟩ := h455c
                            linarith only [hlam, p455_0]
                        · linarith only [h0, h387, h446, h448, h453, h454, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h283, h445, h448, h453, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                  · linarith only [h283, h445, h450, hlam]
              · linarith only [h0, h387, h447, hlam]
            · linarith only [h0, h387, h446, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
            · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
              · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                · linarith only [h388, h488, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                  · linarith only [h445, h488, h490, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                    · linarith only [h488, h492, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                      · linarith only [h387, h490, h494, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                        · linarith only [h283, h490, h496, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h4bigk with h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h283, hlam, p498_1]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h283, h488, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p498_1, u3elo3, u4ehi2]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h388, hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h445, hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h488, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p498_1, u3elo3, u4ehi0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h488, h496, hc45, hlam, hphi, p498_1, u4ehi2]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h488, hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h490, hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h387, hlam, p498_1]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h487, hlam, p498_1]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h492, hlam, p498_1]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h494, hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h387, h496, hc45, hlam, hphi, p498_1, u4ehi2]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h496, hc45, hlam, hphi, p498_1, u4ehi1]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h496, hc45, hlam, hphi, p498_1, u4ehi2]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h496, hlam, p498_0]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h387, hc45, hlam, hphi, p498_1, u4ehi2]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [h283, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p498_1]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hc45, hlam, hphi, p498_1, u4ehi2]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hc45, hlam, hphi, p498_1, u4ehi3]
                          · obtain ⟨p498_0, p498_1, p498_2, p498_3⟩ := h498c
                            linarith only [hlam, p498_0]
              · linarith only [h0, h387, h388, h487, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h387, h486, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h526 | h526
        · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
          · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
            · rcases m.htr 1 2 4 (by decide) (by decide) with h529 | h529
              · rcases m.htr 1 3 4 (by decide) (by decide) with h530 | h530
                · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                        · linarith only [h526, h534, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h387, h527, h529, h530, h534, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
                      · linarith only [h387, h527, h533, hlam]
                    · linarith only [h526, h532, hc23, hlam, hphi, u3elo0]
                  · linarith only [h387, h527, h529, h531, hlam]
                · linarith only [h526, h530, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                · linarith only [h528, h529, h541, hlam]
                · linarith only [h526, h541, hc13, hlam, hphi, u3elo0]
            · linarith only [h0, h528, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
            · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
              · rcases m.htr 1 3 4 (by decide) (by decide) with h547 | h547
                · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
                  · linarith only [h527, h547, h548, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h551 | h551
                      · linarith only [h283, h548, h551, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h553 | h553
                        · linarith only [h0, h387, h546, h548, h550, h553, hc01, hc23, hlam, hphi, ht12]
                        · rcases h4bigk with h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c | h555c
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h283, hlam, p555_1]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h387, hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h387, h546, h548, hc45, hlam, hphi, p555_1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h527, hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h548, hc45, hlam, hphi, p555_1, u4ehi0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h0, h387, h548, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p555_1]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h548, hc45, hlam, hphi, p555_1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h548, hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h526, h546, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p555_1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h546, hlam, p555_1]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h546, h548, hc45, hlam, hphi, p555_1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h551, hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h526, hlam, p555_1]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h547, hlam, p555_1]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h550, hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h553, hlam, p555_0]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h526, hc45, hlam, hphi, p555_1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hc45, hlam, hphi, p555_1, u4ehi1]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [h0, h387, h545, h550, hc01, hc45, hlam, hphi, ht12, ht23, p555_1, u3elo1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hc45, hlam, hphi, p555_1, u4ehi3]
                          · obtain ⟨p555_0, p555_1, p555_2, p555_3⟩ := h555c
                            linarith only [hlam, p555_0]
                    · linarith only [h526, h550, hc23, hlam, hphi, u3elo0]
                · linarith only [h526, h547, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                · linarith only [h545, h546, h583, hlam]
                · linarith only [h526, h583, hc13, hlam, hphi, u3elo0]
            · linarith only [h0, h545, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h587 | h587
          · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
            · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
              · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                · linarith only [h526, h590, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h592 | h592
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                    · linarith only [h588, h590, h593, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h595 | h595
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h596 | h596
                        · rcases h4bigk with h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c | h597c
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h283, hlam, p597_1]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h387, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h526, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h387, h589, h590, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h590, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h590, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi2]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h590, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h590, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h587, h589, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p597_1, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h589, hlam, p597_1]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h593, hlam, p597_1]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h589, h590, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h587, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi1]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h387, h587, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p597_1, u3elo3, u4ehi4]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h587, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h592, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h595, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [h596, hlam, p597_0]
                          · obtain ⟨p597_0, p597_1, p597_2, p597_3⟩ := h597c
                            linarith only [hlam, p597_0]
                        · linarith only [h526, h587, h596, hlam]
                      · linarith only [h387, h587, h595, hlam]
                  · linarith only [h387, h587, h589, h592, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h626 | h626
                · linarith only [h526, h626, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h629 | h629
                    · linarith only [h626, h629, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h589, h629, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h283, h587, h628, hlam]
            · linarith only [h0, h588, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
            · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
              · rcases m.htr 1 3 4 (by decide) (by decide) with h636 | h636
                · linarith only [h526, h636, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h587, h636, h638, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                    · linarith only [h634, h636, h640, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                      · linarith only [h635, h638, h642, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h644 | h644
                        · linarith only [h638, h644, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
                        · rcases h4bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h283, hlam, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h387, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h526, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h587, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h636, h644, hc45, hlam, hphi, p646_1, u4ehi0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h0, h387, hc01, hc14, hlam, hphi, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h636, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h638, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h635, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p646_1, u4ehi0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h635, hlam, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h640, hlam, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h642, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h644, hc45, hlam, hphi, p646_1, u4ehi0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h644, hc45, hlam, hphi, p646_1, u4ehi1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h0, h387, h644, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h644, hlam, p646_0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hc45, hlam, hphi, p646_1, u4ehi0]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hc45, hlam, hphi, p646_1, u4ehi1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h0, h387, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [h636, hc13, hc45, hlam, hphi, ht34, p646_1]
                          · obtain ⟨p646_0, p646_1, p646_2, p646_3⟩ := h646c
                            linarith only [hlam, p646_0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h672 | h672
                · linarith only [h526, h672, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h674 | h674
                  · linarith only [h587, h672, h674, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h676 | h676
                    · linarith only [h672, h676, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h635, h676, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h634, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem n7l_sAB3_M_IR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h3elo := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h10, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h10, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi3]
                    · linarith only [h0, h2, h6, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi2]
                  · linarith only [h3, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h2, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h2, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
            · linarith only [h2, h5, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h1, h23, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h18, h25, h4, hlam]
                      · rcases h4bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h18, h4, hc45, hlam, hphi, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h4, hc45, hlam, hphi, p27_1, u4ehi2]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h4, hc45, hlam, hphi, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h4, hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h0, hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h0, h21, hc01, hlam, hphi, ht0b, ht45, ht5b, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h0, h4, hc45, hlam, hphi, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h19, hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h1, hlam, p27_1]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p27_1, u4ehi1]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h23, hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h2, hlam, p27_1]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h18, hlam, p27_1]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h21, hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h25, hlam, p27_0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hc45, hlam, hphi, p27_1, u4ehi0]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [h18, hc45, hlam, hphi, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hc45, hlam, hphi, p27_1, u4ehi2]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hc45, hlam, hphi, p27_1, u4ehi3]
                        · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                          linarith only [hlam, p27_0]
                  · linarith only [h22, h3, hc23, hlam, hphi, u3elo0]
                · linarith only [h18, h21, hc23, hlam, hphi, u3elo1]
            · linarith only [h18, h2, hc13, hlam, hphi, u3elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
        · linarith only [h2, h57, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h59 | h59
          · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
            · linarith only [h2, h59, h60, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h2, h62, h63, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h57, h63, h65, hc03, hlam, hphi, u3elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                      · rcases h4bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h62, hc04, hlam, hphi, ht0b, ht45, ht5b, p69_1, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi2]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h2, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h0, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h67, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p69_1, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h60, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h1, hlam, p69_1]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p69_1, u4ehi1]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h63, hlam, p69_1]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h62, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi2]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p69_1, u3elo3, u4ehi4]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h59, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h62, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h67, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [h68, hlam, p69_0]
                        · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                          linarith only [hlam, p69_0]
                      · linarith only [h0, h60, h62, h68, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h62, h67, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · linarith only [h2, h59, h62, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
            · linarith only [h2, h98, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
              · linarith only [h0, h100, h59, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                · linarith only [h102, h98, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h102, h104, h57, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h1, h106, h59, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                      · linarith only [h0, h108, h59, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
                      · rcases h4bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p110_1, u3elo3, u4ehi1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p110_1, u3elo3, u4ehi2]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h2, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h59, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h0, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p110_1, u4ehi2]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h98, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h100, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h1, hlam, p110_1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h1, hc02, hlam, hphi, ht0b, ht45, ht5b, p110_1, u4ehi1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h102, hlam, p110_1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h106, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h108, hc45, hlam, hphi, p110_1, u4ehi0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h108, hc45, hlam, hphi, p110_1, u4ehi1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h108, hc45, hlam, hphi, p110_1, u4ehi2]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h108, hlam, p110_0]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h1, hc45, hlam, hphi, p110_1, u4ehi2]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hc45, hlam, hphi, p110_1, u4ehi1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hc45, hlam, hphi, p110_1, u4ehi2]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [h2, hc03, hc45, hlam, hphi, ht34, p110_1]
                        · obtain ⟨p110_0, p110_1, p110_2, p110_3⟩ := h110c
                          linarith only [hlam, p110_0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
      · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
        · rcases m.htr 0 4 5 (by decide) (by decide) with h138 | h138
          · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
              · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h143 | h143
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                      · linarith only [h136, h144, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h0, h140, h144, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h1, h140, h143, hlam]
                  · linarith only [h1, h137, h141, h142, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi0]
                · linarith only [h136, h141, hc23, hlam, hphi, u3elo0]
              · linarith only [h136, h138, h140, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
            · linarith only [h136, h139, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
            · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
              · linarith only [h0, h138, h153, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                    · linarith only [h0, h138, h152, h155, h157, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h159 | h159
                      · linarith only [h1, h136, h157, h159, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h4bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h1, h152, h157, hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h1, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h1, h157, hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h138, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h0, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h0, h1, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p161_1]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h153, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h155, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p161_1, u3elo2, u4ehi0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h152, h157, hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h157, hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h157, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h136, hlam, p161_1]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h152, hlam, p161_1]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h155, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h159, hlam, p161_0]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h0, h152, hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [h152, hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hc45, hlam, hphi, p161_1, u4ehi2]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hc45, hlam, hphi, p161_1, u4ehi3]
                        · obtain ⟨p161_0, p161_1, p161_2, p161_3⟩ := h161c
                          linarith only [hlam, p161_0]
                  · linarith only [h137, h156, hc23, hlam, hphi, u3elo0]
                · linarith only [h136, h155, hc23, hlam, hphi, u3elo0]
            · linarith only [h136, h152, hc13, hlam, hphi, u3elo0]
        · linarith only [h136, h137, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
        · linarith only [h136, h191, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
          · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
            · linarith only [h136, h194, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
              · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                · linarith only [h0, h136, h196, h197, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                  · linarith only [h191, h197, h199, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                      · rcases h4bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h196, hc04, hlam, hphi, ht0b, ht45, ht5b, p203_1, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h1, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h136, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h136, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h0, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h0, h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p203_1, u4ehi0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h194, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h0, h136, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h193, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p203_1, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h196, h197, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h197, hlam, p203_1]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h197, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h0, h196, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h196, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi2]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p203_1, u3elo3, u4ehi4]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h193, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h196, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h201, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [h202, hlam, p203_0]
                        · obtain ⟨p203_0, p203_1, p203_2, p203_3⟩ := h203c
                          linarith only [hlam, p203_0]
                      · linarith only [h0, h194, h196, h202, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h196, h201, hlam]
              · linarith only [h136, h193, h196, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
            · linarith only [h136, h232, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
              · linarith only [h0, h193, h234, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                · linarith only [h232, h236, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                  · linarith only [h236, h238, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h240 | h240
                    · linarith only [h0, h193, h236, h240, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h242 | h242
                      · linarith only [h1, h240, h242, hc02, hlam, hphi, ht23, u3elo3]
                      · rcases h4bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h136, h242, hc45, hlam, hphi, p244_1, u4ehi1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h1, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h136, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h193, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h0, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h0, h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p244_1, u4ehi0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h232, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h234, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h236, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p244_1, u3elo3, u4ehi0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h236, h242, hc45, hlam, hphi, p244_1, u4ehi1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h236, hlam, p244_1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h240, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h0, h242, hc45, hlam, hphi, p244_1, u4ehi1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h242, hc45, hlam, hphi, p244_1, u4ehi1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h242, hc45, hlam, hphi, p244_1, u4ehi2]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h242, hlam, p244_0]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h0, hc45, hlam, hphi, p244_1, u4ehi1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [hc45, hlam, hphi, p244_1, u4ehi1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p244_1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [h136, hc03, hc45, hlam, hphi, ht34, p244_1]
                        · obtain ⟨p244_0, p244_1, p244_2, p244_3⟩ := h244c
                          linarith only [hlam, p244_0]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h270 | h270
    · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
      · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
        · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
          · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
            · rcases m.htr 1 4 5 (by decide) (by decide) with h275 | h275
              · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                      · linarith only [h271, h279, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h270, h278, h279, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h273, h274, h278, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi2]
                  · linarith only [h276, h277, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                · linarith only [h271, h276, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h273, h275, hlam]
            · linarith only [h271, h274, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
            · rcases m.htr 1 4 5 (by decide) (by decide) with h288 | h288
              · linarith only [h0, h273, h287, h288, hc01, hlam, hphi, ht12, ht23, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h292 | h292
                    · linarith only [h0, h288, h292, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                      · linarith only [h0, h288, h290, h294, hc01, hc23, hlam, hphi, ht12]
                      · rcases h4bigk with h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c | h296c
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h0, hlam, p296_1]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h0, h288, hc45, hlam, hphi, p296_1, u4ehi2]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h0, h288, hc45, hlam, hphi, p296_1, u4ehi3]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h273, hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h288, hc45, hlam, hphi, p296_1, u4ehi0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h288, h290, hc45, hlam, hphi, p296_1, u4ehi3]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h288, hc45, hlam, hphi, p296_1, u4ehi3]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h288, hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h270, hlam, p296_1]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p296_1]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h270, hc02, hlam, hphi, ht0b, ht45, ht5b, p296_1, u4ehi3]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h292, hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h271, hlam, p296_1]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h287, hlam, p296_1]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h290, hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h294, hlam, p296_0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hc45, hlam, hphi, p296_1, u4ehi0]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p296_1]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [h290, hc45, hlam, hphi, p296_1, u4ehi3]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hc45, hlam, hphi, p296_1, u4ehi3]
                        · obtain ⟨p296_0, p296_1, p296_2, p296_3⟩ := h296c
                          linarith only [hlam, p296_0]
                  · linarith only [h272, h291, hc23, hlam, hphi, u3elo0]
                · linarith only [h271, h290, hc23, hlam, hphi, u3elo0]
            · linarith only [h271, h287, hc13, hlam, hphi, u3elo0]
        · linarith only [h271, h272, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h326 | h326
        · linarith only [h271, h326, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
          · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
            · linarith only [h271, h329, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
              · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                · linarith only [h329, h332, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
                  · linarith only [h0, h270, h326, h329, h332, h334, hc03, hlam, hphi, u3elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                      · rcases h4bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h0, hlam, p338_1]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h0, h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi2]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h271, hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h0, h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p338_1, u3elo3, u5ehi4]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h329, h336, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi4]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h329, hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi4]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h270, hlam, p338_1]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p338_1]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h332, hlam, p338_1]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h0, h270, h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi4]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi1]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi2]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p338_1, u3elo3, u4ehi4]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h328, hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h331, hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h336, hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [h337, hlam, p338_0]
                        · obtain ⟨p338_0, p338_1, p338_2, p338_3⟩ := h338c
                          linarith only [hlam, p338_0]
                      · linarith only [h270, h336, h337, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h328, h329, h336, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · linarith only [h0, h328, h331, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h367 | h367
            · linarith only [h271, h367, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
              · linarith only [h328, h367, h369, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                · linarith only [h367, h371, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
                  · linarith only [h326, h371, h373, hc03, hlam, hphi, u3elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                    · linarith only [h270, h328, h375, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h377 | h377
                      · linarith only [h0, h369, h377, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases h4bigk with h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h0, hlam, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h271, h377, hc45, hlam, hphi, p379_1, u4ehi2]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h271, hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h328, hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h367, h377, hc45, hlam, hphi, p379_1, u4ehi0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h367, h377, hc45, hlam, hphi, p379_1, u4ehi2]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h367, hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h369, hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h270, hlam, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h371, hlam, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h375, hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h377, hc45, hlam, hphi, p379_1, u4ehi0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h0, h377, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h377, hc45, hlam, hphi, p379_1, u4ehi2]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h377, hlam, p379_0]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h270, hc45, hlam, hphi, p379_1, u4ehi2]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [hc45, hlam, hphi, p379_1, u4ehi2]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [h367, hc13, hc45, hlam, hphi, ht34, p379_1]
                        · obtain ⟨p379_0, p379_1, p379_2, p379_3⟩ := h379c
                          linarith only [hlam, p379_0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
      · rcases m.htr 0 3 5 (by decide) (by decide) with h406 | h406
        · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
          · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
            · rcases m.htr 1 4 5 (by decide) (by decide) with h409 | h409
              · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                · rcases m.htr 2 3 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                      · linarith only [h405, h413, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h405, h407, h413, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi3]
                    · linarith only [h270, h407, h412, hlam]
                  · linarith only [h270, h406, h410, h411, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi0]
                · linarith only [h405, h410, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h270, h407, h409, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h405, h408, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
            · rcases m.htr 1 4 5 (by decide) (by decide) with h422 | h422
              · linarith only [h407, h421, h422, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                · rcases m.htr 2 3 5 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h426 | h426
                    · linarith only [h422, h424, h426, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h428 | h428
                      · linarith only [h0, h405, h422, h428, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h4bigk with h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h0, hlam, p430_1]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h270, hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h0, h422, hc45, hlam, hphi, p430_1, u4ehi3]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h407, hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h422, hc45, hlam, hphi, p430_1, u4ehi0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h422, hc45, hlam, hphi, p430_1, u4ehi2]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h422, hc45, hlam, hphi, p430_1, u4ehi3]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h422, hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h405, h424, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p430_1, u3elo2, u4ehi3]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h0, h426, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p430_1]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h426, hc45, hlam, hphi, p430_1, u4ehi3]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h426, hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h405, hlam, p430_1]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h421, hlam, p430_1]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h424, hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h428, hlam, p430_0]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h405, hc45, hlam, hphi, p430_1, u4ehi3]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p430_1]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hc45, hlam, hphi, p430_1, u4ehi2]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hc45, hlam, hphi, p430_1, u4ehi3]
                        · obtain ⟨p430_0, p430_1, p430_2, p430_3⟩ := h430c
                          linarith only [hlam, p430_0]
                  · linarith only [h406, h425, hc23, hlam, hphi, u3elo0]
                · linarith only [h405, h424, hc23, hlam, hphi, u3elo0]
            · linarith only [h405, h421, hc13, hlam, hphi, u3elo0]
        · linarith only [h405, h406, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h460 | h460
        · linarith only [h405, h460, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
          · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
            · linarith only [h405, h463, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
              · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                · linarith only [h463, h466, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                  · linarith only [h460, h466, h468, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                      · rcases h4bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h0, hlam, p472_1]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h270, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h405, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h405, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h462, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p472_1, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h270, h462, h463, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h463, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h463, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h462, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p472_1, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h466, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi1]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h466, hlam, p472_1]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h466, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h462, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h0, h462, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi2]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p472_1, u3elo3, u4ehi4]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h462, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h465, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h470, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [h471, hlam, p472_0]
                        · obtain ⟨p472_0, p472_1, p472_2, p472_3⟩ := h472c
                          linarith only [hlam, p472_0]
                      · linarith only [h405, h462, h471, hlam]
                    · linarith only [h0, h462, h463, h470, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · linarith only [h0, h462, h465, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
            · linarith only [h405, h501, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
              · linarith only [h462, h501, h503, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                · linarith only [h501, h505, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                  · linarith only [h505, h507, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                    · linarith only [h0, h503, h509, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h511 | h511
                      · linarith only [h0, h503, h511, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases h4bigk with h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h0, hlam, p513_1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h270, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h405, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h462, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h501, h511, hc45, hlam, hphi, p513_1, u4ehi0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h501, h511, hc45, hlam, hphi, p513_1, u4ehi2]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h501, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h503, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h505, h511, hc45, hlam, hphi, p513_1, u4ehi0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h505, h511, hc45, hlam, hphi, p513_1, u4ehi1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h505, hlam, p513_1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h509, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h511, hc45, hlam, hphi, p513_1, u4ehi0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h0, h511, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p513_1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h511, hc45, hlam, hphi, p513_1, u4ehi2]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h511, hlam, p513_0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [hc45, hlam, hphi, p513_1, u4ehi0]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p513_1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h270, hc02, hc45, hlam, hphi, ht23, ht34, p513_1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [h505, hc23, hc45, hlam, hphi, ht34, p513_1]
                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                          linarith only [hlam, p513_0]

theorem n7l_sAB3_M_IR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h3bigk := hb3.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h12, h5, h9, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h12, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h0, h11, h6, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h10, h3, h9, hlam, hphi, ht45, u4ehi3, u5elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h17, h2, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h19, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · linarith only [h19, hlam, hphi, ht45, u4ehi2, u5elo4]
                  · linarith only [h4, h8, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h6, h7, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h2, h24, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                    · linarith only [h1, h26, h27, h6, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h24, h29, h5, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                          · rcases h3bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              rcases p33_3 (m.d 0 3) (by simp) with h35 | h35
                              · rcases p33_3 (m.d 1 3) (by simp) with h36 | h36
                                · linarith only [h0, h36, hlam]
                                · rcases p33_3 (m.d 2 3) (by simp) with h38 | h38
                                  · linarith only [h1, h38, hlam]
                                  · rcases p33_3 (m.d 3 4) (by simp) with h40 | h40
                                    · linarith only [h2, h40, hlam]
                                    · linarith only [h40, h6, hlam]
                              · linarith only [h0, h35, hlam]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              rcases p33_3 (m.d 0 3) (by simp) with h44 | h44
                              · rcases p33_3 (m.d 1 3) (by simp) with h45 | h45
                                · linarith only [h0, h45, hlam]
                                · linarith only [h45, h5, hlam]
                              · linarith only [h1, h44, hlam]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h26, h6, hc03, hlam, hphi, ht0b, ht45, ht5b, p33_1, u4ehi4]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              rcases p33_3 (m.d 0 3) (by simp) with h50 | h50
                              · rcases p33_3 (m.d 1 3) (by simp) with h51 | h51
                                · linarith only [h0, h51, hlam]
                                · rcases p33_3 (m.d 2 3) (by simp) with h53 | h53
                                  · linarith only [h1, h53, hlam]
                                  · rcases p33_3 (m.d 3 4) (by simp) with h55 | h55
                                    · linarith only [h2, h55, hlam]
                                    · linarith only [h32, h55, hlam]
                              · linarith only [h50, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h0, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h24, hc23, hc35, hlam, hphi, p33_1]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h6, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h24, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h1, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h5, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h27, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h29, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h2, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              rcases p33_3 (m.d 0 3) (by simp) with h70 | h70
                              · rcases p33_3 (m.d 1 3) (by simp) with h71 | h71
                                · linarith only [h71, hlam, p33_0]
                                · rcases p33_3 (m.d 2 3) (by simp) with h73 | h73
                                  · linarith only [h27, h73, hlam]
                                  · rcases p33_3 (m.d 3 4) (by simp) with h75 | h75
                                    · rcases p33_3 (m.d 3 5) (by simp) with h76 | h76
                                      · linarith only [h32, h76, hlam]
                                      · linarith only [h24, h76, hlam]
                                    · linarith only [h75, hlam, p33_0]
                              · linarith only [h0, h70, hlam]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              rcases p33_3 (m.d 0 3) (by simp) with h81 | h81
                              · rcases p33_3 (m.d 1 3) (by simp) with h82 | h82
                                · linarith only [h6, h82, hlam]
                                · linarith only [h5, h82, hlam]
                              · linarith only [h1, h81, hlam]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h0, h2, h24, hc01, hlam, hphi, ht0b, ht5b, p33_1, u5ehi6]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h3, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h5, hc23, hlam, hphi, ht34, ht45, p33_1, u5elo3]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h3, hc23, hlam, hphi, ht34, ht45, p33_1, u5elo0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [h32, hlam, p33_0]
                            · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                              linarith only [hlam, p33_0]
                          · linarith only [h26, h32, hlam, hphi, ht45, u4ehi3, u5elo1]
                        · linarith only [h0, h2, h26, h31, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h26, hlam, hphi, ht45, u4ehi1, u5elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
                · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h0, h102, h96, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h102, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h1, h101, h5, h96, h98, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h100, h5, h97, hlam]
                    · linarith only [h0, h2, h5, h97, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h98, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h96, h97, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h110, h2, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                    · linarith only [h1, h112, h113, h96, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h110, h113, h115, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h115, h3, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                  · linarith only [h112, hlam, hphi, ht45, u4ehi1, u5elo4]
          · linarith only [h4, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h2, h3, hlam, hphi, ht45, u4ehi3, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
        · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
          · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
            · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
              · linarith only [h0, h124, h2, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                    · linarith only [h0, h123, h128, h2, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                          · rcases h3bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h123, h130, h132, hc03, hlam, hphi, ht0b, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h130, h132, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h2, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h132, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h0, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h130, h132, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h124, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h0, h132, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h1, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h123, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h128, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h123, h132, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h121, h132, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h126, h132, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h130, h132, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u4ehi4]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              rcases p133_3 (m.d 0 3) (by simp) with h153 | h153
                              · linarith only [h153, h2, hlam]
                              · linarith only [h121, h153, hlam]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h121, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h126, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h130, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [h132, hlam, p133_0]
                            · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                              linarith only [hlam, p133_0]
                          · linarith only [h132, h2, hlam, hphi, ht45, u4ehi0, u5elo4]
                        · linarith only [h122, h131, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h121, h130, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h122, h127, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h121, h126, h2, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
              · linarith only [h121, h166, h2, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                    · linarith only [h1, h170, h2, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                          · rcases h3bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h168, h174, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h123, h168, h174, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h2, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h174, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h0, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h123, hlam, p175_1]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h166, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h0, h174, hc01, hlam, hphi, ht0b, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h1, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h1, h2, hc13, hc34, hlam, hphi, p175_1]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h170, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h1, h174, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h0, h168, h174, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h168, h174, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h123, h168, h174, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p175_1, u4ehi4]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              rcases p175_3 (m.d 0 3) (by simp) with h195 | h195
                              · linarith only [h195, h2, hlam]
                              · linarith only [h121, h195, hlam]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h121, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h168, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h172, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [h174, hlam, p175_0]
                            · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                              linarith only [hlam, p175_0]
                          · linarith only [h170, h174, hlam, hphi, ht45, u4ehi2, u5elo4]
                        · linarith only [h122, h173, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h123, h168, h172, hlam]
                  · linarith only [h122, h169, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h121, h168, h2, hc13, hc34, hlam, hphi]
          · linarith only [h122, hlam, hphi, ht45, u4ehi0, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h209 | h209
          · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
            · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
              · linarith only [h0, h121, h211, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h213 | h213
                · linarith only [h0, h121, h213, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                    · linarith only [h2, h209, h210, h216, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                      · linarith only [h0, h121, h210, h218, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                          · rcases h3bigk with h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h121, hc13, hlam, hphi, ht34, ht45, p222_1, u5elo3]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h121, hc23, hlam, hphi, ht34, ht45, p222_1, u5elo3]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h2, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h121, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h0, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h0, h121, hc23, hlam, hphi, ht34, ht45, p222_1, u5elo3]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h211, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h213, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h1, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h210, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h216, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h218, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              rcases p222_3 (m.d 0 3) (by simp) with h238 | h238
                              · linarith only [h238, hlam, p222_0]
                              · rcases p222_3 (m.d 1 3) (by simp) with h240 | h240
                                · linarith only [h211, h240, hlam]
                                · rcases p222_3 (m.d 2 3) (by simp) with h242 | h242
                                  · linarith only [h216, h242, hlam]
                                  · rcases p222_3 (m.d 3 4) (by simp) with h244 | h244
                                    · rcases p222_3 (m.d 3 5) (by simp) with h245 | h245
                                      · linarith only [h221, h245, hlam]
                                      · linarith only [h121, h245, hlam]
                                    · linarith only [h244, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              rcases p222_3 (m.d 0 3) (by simp) with h249 | h249
                              · linarith only [h2, h249, hlam]
                              · linarith only [h0, h249, hlam]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              rcases p222_3 (m.d 0 3) (by simp) with h252 | h252
                              · linarith only [h2, h252, hlam]
                              · linarith only [h1, h252, hlam]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h121, hc03, hc34, hlam, hphi, p222_1]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h0, hc13, hlam, hphi, ht34, ht45, p222_1, u5elo3]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h210, hc23, hlam, hphi, ht34, ht45, p222_1, u5elo3]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [hc23, hlam, hphi, ht34, ht45, p222_1, u5elo3]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [h221, hlam, p222_0]
                            · obtain ⟨p222_0, p222_1, p222_2, p222_3⟩ := h222c
                              linarith only [hlam, p222_0]
                          · linarith only [h216, h220, h221, hlam, hphi, ht45, u4ehi2, u5elo2]
                        · linarith only [h121, h209, h220, hlam, hphi, ht45, u4ehi2, u5elo3]
                  · linarith only [h121, h209, h215, hlam, hphi, ht45, u4ehi1, u5elo3]
            · linarith only [h1, h121, h210, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h209, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
      · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
        · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
          · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
            · linarith only [h0, h1, h270, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
              · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                          · linarith only [h0, h272, h278, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h278, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h0, h272, h274, h277, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1, h267, h268, h276, hlam, hphi, ht45, u4ehi0, u5elo0]
                    · linarith only [h1, h267, h275, hlam]
                  · linarith only [h274, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h268, h272, h273, hlam, hphi, ht45, u4ehi3, u5elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h286 | h286
                · linarith only [h267, h272, h286, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h290 | h290
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h291 | h291
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
                          · rcases h3bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              rcases p293_3 (m.d 0 3) (by simp) with h295 | h295
                              · rcases p293_3 (m.d 1 3) (by simp) with h296 | h296
                                · linarith only [h0, h296, hlam]
                                · rcases p293_3 (m.d 2 3) (by simp) with h298 | h298
                                  · rcases p293_3 (m.d 3 4) (by simp) with h299 | h299
                                    · linarith only [h267, h299, hlam]
                                    · linarith only [h272, h299, hlam]
                                  · linarith only [h270, h298, hlam]
                              · linarith only [h0, h295, hlam]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h1, hlam, p293_1]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h1, h272, h288, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi4]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h1, h270, h286, hc12, hc23, hlam, hphi, p293_1]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h0, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h270, hlam, p293_1]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h272, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h286, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h267, h272, h288, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi4]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              rcases p293_3 (m.d 0 3) (by simp) with h313 | h313
                              · linarith only [h1, h313, hlam]
                              · linarith only [h0, h313, hlam]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h272, h288, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u4ehi4]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h270, h286, hc12, hc23, hlam, hphi, p293_1]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h267, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h1, h267, h270, hc12, hc23, hlam, hphi, p293_1]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h289, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h1, h267, h270, h286, hc12, hc23, hlam, hphi, p293_1]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h268, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h270, hc12, hlam, hphi, ht23, ht34, ht45, p293_1, u5elo3]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h290, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [h292, hlam, p293_0]
                            · obtain ⟨p293_0, p293_1, p293_2, p293_3⟩ := h293c
                              linarith only [hlam, p293_0]
                          · linarith only [h272, h288, h292, hlam]
                        · linarith only [h272, h288, h289, h291, hlam]
                      · linarith only [h1, h267, h268, h272, h288, h290, hlam, hphi, ht45, u4ehi4, u5elo0]
                    · linarith only [h1, h267, h289, hlam]
                  · linarith only [h288, hlam, hphi, ht45, u4ehi1, u5elo4]
          · linarith only [h269, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h267, h268, hlam, hphi, ht45, u4ehi3, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h336 | h336
        · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
          · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
            · linarith only [h0, h1, h338, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
              · linarith only [h0, h267, h340, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
                · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                    · linarith only [h267, h336, h344, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h347 | h347
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                          · rcases h3bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h342, h348, hc03, hlam, hphi, ht0b, ht45, ht5b, p349_1, u4ehi4]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h1, hlam, p349_1]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h267, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h1, h344, h348, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p349_1, u4ehi4]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h0, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h338, hlam, p349_1]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h340, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h0, h348, hc01, hlam, hphi, ht0b, ht45, ht5b, p349_1, u4ehi4]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h344, hc03, hc34, hlam, hphi, p349_1]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h344, hc13, hc34, hlam, hphi, p349_1]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h344, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h344, h348, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p349_1, u4ehi4]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h0, h342, h348, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p349_1, u4ehi4]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h342, h348, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p349_1, u4ehi4]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h1, hc02, hc34, hlam, hphi, ht23, p349_1]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              rcases p349_3 (m.d 0 3) (by simp) with h369 | h369
                              · linarith only [h267, h369, hlam]
                              · linarith only [h336, h369, hlam]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h336, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h342, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h346, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [h348, hlam, p349_0]
                            · obtain ⟨p349_0, p349_1, p349_2, p349_3⟩ := h349c
                              linarith only [hlam, p349_0]
                          · linarith only [h267, h348, hlam, hphi, ht45, u4ehi0, u5elo4]
                        · linarith only [h337, h347, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h0, h1, h342, h346, hlam]
                  · linarith only [h337, h343, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h267, h336, h342, hc13, hc34, hlam, hphi]
          · linarith only [h337, hlam, hphi, ht45, u4ehi0, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
          · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
            · linarith only [h0, h1, h336, h384, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h386 | h386
              · linarith only [h0, h336, h386, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                · linarith only [h0, h336, h388, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h394 | h394
                          · rcases h3bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h336, h384, h392, hc12, hlam, hphi, ht23, ht34, ht45, p395_1, u5elo2]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h1, hlam, p395_1]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h267, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h336, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h0, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h384, hlam, p395_1]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h386, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h388, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              rcases p395_3 (m.d 0 3) (by simp) with h406 | h406
                              · linarith only [h1, h406, hlam]
                              · rcases p395_3 (m.d 1 3) (by simp) with h408 | h408
                                · linarith only [h384, h408, hlam]
                                · rcases p395_3 (m.d 2 3) (by simp) with h410 | h410
                                  · rcases p395_3 (m.d 3 4) (by simp) with h411 | h411
                                    · linarith only [h391, h411, hlam]
                                    · linarith only [h267, h411, hlam]
                                  · linarith only [h1, h410, hlam]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              rcases p395_3 (m.d 0 3) (by simp) with h415 | h415
                              · linarith only [h1, h415, hlam]
                              · linarith only [h0, h415, hlam]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h267, h383, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p395_1, u5ehi9]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h0, h336, h384, hc12, hc23, hlam, hphi, p395_1]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h0, h384, h391, hc12, hc23, hlam, hphi, p395_1]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h384, h391, hc12, hc23, hlam, hphi, p395_1]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h391, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h0, h336, h384, h391, hc12, hc23, hlam, hphi, p395_1]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h0, h384, h392, hc12, hlam, hphi, ht23, ht34, ht45, p395_1, u5elo2]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h384, h392, hc12, hlam, hphi, ht23, ht34, ht45, p395_1, u5elo2]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h392, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [h394, hlam, p395_0]
                            · obtain ⟨p395_0, p395_1, p395_2, p395_3⟩ := h395c
                              linarith only [hlam, p395_0]
                          · linarith only [h394, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h267, h383, h391, h393, hlam]
                      · linarith only [h267, h383, h391, h392, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h434 | h434
                      · linarith only [h0, h336, h384, h391, h434, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h434, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h390, hlam, hphi, ht45, u4ehi1, u5elo4]
          · linarith only [h383, hlam, hphi, ht45, u4ehi0, u5elo4]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h439 | h439
    · rcases m.htr 0 3 4 (by decide) (by decide) with h440 | h440
      · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
        · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
          · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
            · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
              · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                          · linarith only [h439, h447, h450, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h450, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h442, h449, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h441, h447, h448, hlam, hphi, ht45, u4ehi3, u5elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                      · linarith only [h440, h447, h455, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                          · rcases h3bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h0, hlam, p459_1]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              rcases p459_3 (m.d 0 3) (by simp) with h462 | h462
                              · rcases p459_3 (m.d 1 3) (by simp) with h463 | h463
                                · rcases p459_3 (m.d 2 3) (by simp) with h464 | h464
                                  · linarith only [h439, h464, hlam]
                                  · rcases p459_3 (m.d 3 4) (by simp) with h466 | h466
                                    · linarith only [h440, h466, hlam]
                                    · linarith only [h447, h466, hlam]
                                · linarith only [h443, h463, hlam]
                              · linarith only [h439, h462, hlam]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h0, h443, h447, h457, hc12, hlam, hphi, ht01, ht0b, ht5b, p459_1, u5ehi9]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              rcases p459_3 (m.d 0 3) (by simp) with h472 | h472
                              · rcases p459_3 (m.d 1 3) (by simp) with h473 | h473
                                · rcases p459_3 (m.d 2 3) (by simp) with h474 | h474
                                  · linarith only [h439, h474, hlam]
                                  · rcases p459_3 (m.d 3 4) (by simp) with h476 | h476
                                    · linarith only [h440, h476, hlam]
                                    · linarith only [h458, h476, hlam]
                                · linarith only [h445, h473, hlam]
                              · linarith only [h472, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h440, h443, h447, h457, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p459_1, u4ehi4]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              rcases p459_3 (m.d 0 3) (by simp) with h483 | h483
                              · linarith only [h0, h483, hlam]
                              · linarith only [h439, h483, hlam]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h447, h457, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p459_1, u4ehi4]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              rcases p459_3 (m.d 0 3) (by simp) with h487 | h487
                              · linarith only [h0, h487, hlam]
                              · linarith only [h441, h487, hlam]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h439, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h443, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h447, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h455, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h440, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h444, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              rcases p459_3 (m.d 0 3) (by simp) with h497 | h497
                              · rcases p459_3 (m.d 1 3) (by simp) with h498 | h498
                                · rcases p459_3 (m.d 2 3) (by simp) with h499 | h499
                                  · linarith only [h499, hlam, p459_0]
                                  · rcases p459_3 (m.d 3 4) (by simp) with h501 | h501
                                    · rcases p459_3 (m.d 3 5) (by simp) with h502 | h502
                                      · linarith only [h458, h502, hlam]
                                      · linarith only [h455, h502, hlam]
                                    · linarith only [h501, hlam, p459_0]
                                · linarith only [h443, h498, hlam]
                              · linarith only [h439, h497, hlam]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h440, h455, hc03, hlam, hphi, ht0b, ht5b, p459_1, u5ehi7]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h441, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h445, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [hc23, hlam, hphi, ht34, ht45, p459_1, u5elo3]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [h458, hlam, p459_0]
                            · obtain ⟨p459_0, p459_1, p459_2, p459_3⟩ := h459c
                              linarith only [hlam, p459_0]
                          · linarith only [h447, h457, h458, hlam]
                        · linarith only [h457, hlam, hphi, ht45, u4ehi2, u5elo4]
                  · linarith only [h444, h446, hlam, hphi, ht45, u4ehi3, u5elo4]
                · linarith only [h0, h440, h441, h445, hlam, hphi, ht45, u4ehi0, u5elo0]
              · linarith only [h0, h440, h444, hlam]
            · linarith only [h0, h439, h443, hlam]
          · linarith only [h442, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h440, h441, hlam, hphi, ht45, u4ehi3, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h523 | h523
        · rcases m.htr 0 4 5 (by decide) (by decide) with h524 | h524
          · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
            · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
              · linarith only [h440, h523, h526, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                    · linarith only [h0, h526, h530, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                          · rcases h3bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h0, hlam, p535_1]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h0, h526, h532, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h440, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h0, h526, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h526, hc03, hc34, hlam, hphi, p535_1]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h526, h532, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h526, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h526, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h439, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h525, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h530, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h0, h439, h526, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h523, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p535_1]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h532, h534, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u4ehi4]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              rcases p535_3 (m.d 0 3) (by simp) with h555 | h555
                              · linarith only [h440, h555, hlam]
                              · linarith only [h523, h555, hlam]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h523, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h528, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h532, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [h534, hlam, p535_0]
                            · obtain ⟨p535_0, p535_1, p535_2, p535_3⟩ := h535c
                              linarith only [hlam, p535_0]
                          · linarith only [h534, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h524, h533, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h0, h523, h526, h532, hc23, hc34, hlam, hphi]
                  · linarith only [h524, h529, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h0, h523, h528, hlam]
            · linarith only [h0, h439, h525, hlam]
          · linarith only [h524, hlam, hphi, ht45, u4ehi0, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h570 | h570
          · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
            · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
              · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
                · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                    · linarith only [h439, h440, h570, h575, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h577 | h577
                      · linarith only [h439, h523, h577, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h579 | h579
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h580 | h580
                          · rcases h3bigk with h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h0, hlam, p581_1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h523, h573, hc23, hlam, hphi, ht34, ht45, p581_1, u5elo1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h440, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h523, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              rcases p581_3 (m.d 0 3) (by simp) with h587 | h587
                              · linarith only [h0, h587, hlam]
                              · rcases p581_3 (m.d 1 3) (by simp) with h589 | h589
                                · rcases p581_3 (m.d 2 3) (by simp) with h590 | h590
                                  · linarith only [h571, h590, hlam]
                                  · rcases p581_3 (m.d 3 4) (by simp) with h592 | h592
                                    · linarith only [h572, h592, hlam]
                                    · linarith only [h440, h592, hlam]
                                · linarith only [h0, h589, hlam]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              rcases p581_3 (m.d 0 3) (by simp) with h597 | h597
                              · linarith only [h0, h597, hlam]
                              · linarith only [h439, h597, hlam]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h0, h440, h523, h570, h571, h573, hc01, hc12, hlam, hphi, ht45, p581_1, u4ehi4, u5elo1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h0, h523, h571, hc01, hc12, hlam, hphi, p581_1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h439, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h571, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h575, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h577, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h0, h571, h572, hc01, hc12, hlam, hphi, p581_1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h572, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              rcases p581_3 (m.d 0 3) (by simp) with h609 | h609
                              · linarith only [h440, h609, hlam]
                              · linarith only [h439, h609, hlam]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h0, h523, h571, h572, hc01, hc12, hlam, hphi, p581_1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h0, h573, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p581_1, u5elo1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h573, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h573, hc23, hlam, hphi, ht34, ht45, p581_1, u5elo1]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [h580, hlam, p581_0]
                            · obtain ⟨p581_0, p581_1, p581_2, p581_3⟩ := h581c
                              linarith only [hlam, p581_0]
                          · linarith only [h579, h580, hlam, hphi, ht45, u4ehi3, u5elo2]
                        · linarith only [h579, hlam, hphi, ht45, u4ehi2, u5elo4]
                  · linarith only [h440, h570, h572, h574, hlam]
                · linarith only [h440, h570, h572, h573, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
                · linarith only [h0, h523, h572, h623, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h623, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h439, h523, h571, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h570, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h628 | h628
      · rcases m.htr 0 3 5 (by decide) (by decide) with h629 | h629
        · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
          · rcases m.htr 1 2 3 (by decide) (by decide) with h631 | h631
            · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
              · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                · rcases m.htr 1 4 5 (by decide) (by decide) with h634 | h634
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
                          · linarith only [h439, h628, h631, h638, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h638, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h439, h628, h630, h631, h637, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h439, h629, h636, hlam]
                    · linarith only [h439, h628, h635, hlam]
                  · linarith only [h439, h628, h630, h631, h634, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h439, h629, h631, h633, hc01, hc12, hlam, hphi]
              · linarith only [h439, h628, h631, h632, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h647 | h647
              · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
                · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h651 | h651
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h652 | h652
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h653 | h653
                          · rcases h3bigk with h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c | h654c
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h0, hlam, p654_1]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h439, hlam, p654_1]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h0, h631, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p654_1, u5ehi9]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              rcases p654_3 (m.d 0 3) (by simp) with h659 | h659
                              · rcases p654_3 (m.d 1 3) (by simp) with h660 | h660
                                · rcases p654_3 (m.d 2 3) (by simp) with h661 | h661
                                  · rcases p654_3 (m.d 3 4) (by simp) with h662 | h662
                                    · linarith only [h628, h662, hlam]
                                    · linarith only [h653, h662, hlam]
                                  · linarith only [h651, h661, hlam]
                                · linarith only [h648, h660, hlam]
                              · linarith only [h659, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h628, h631, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p654_1, u4ehi4]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h631, hlam, p654_1]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h631, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p654_1, u4ehi4]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              rcases p654_3 (m.d 0 3) (by simp) with h672 | h672
                              · linarith only [h0, h672, hlam]
                              · linarith only [h629, h672, hlam]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h628, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p654_1, u4ehi4]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p654_1]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p654_1, u4ehi4]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              rcases p654_3 (m.d 0 3) (by simp) with h679 | h679
                              · linarith only [h439, h679, hlam]
                              · linarith only [h629, h679, hlam]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h628, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h647, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h650, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h628, h653, hc03, hlam, hphi, ht0b, ht45, ht5b, p654_1, u4ehi4]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h629, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h648, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h651, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [h653, hlam, p654_0]
                            · obtain ⟨p654_0, p654_1, p654_2, p654_3⟩ := h654c
                              linarith only [hlam, p654_0]
                          · linarith only [h653, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h630, h650, h652, hlam, hphi, ht45, u4ehi3, u5elo0]
                      · linarith only [h631, h651, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h628, h631, h650, hlam]
                  · linarith only [h649, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h0, h629, h648, hlam]
              · linarith only [h0, h628, h647, hlam]
          · linarith only [h630, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h628, h629, hlam, hphi, ht45, u4ehi3, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h701 | h701
        · rcases m.htr 0 4 5 (by decide) (by decide) with h702 | h702
          · rcases m.htr 1 2 3 (by decide) (by decide) with h703 | h703
            · rcases m.htr 1 3 4 (by decide) (by decide) with h704 | h704
              · linarith only [h628, h701, h703, h704, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h706 | h706
                · rcases m.htr 1 4 5 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h708 | h708
                    · linarith only [h703, h704, h708, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h710 | h710
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h711 | h711
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h712 | h712
                          · rcases h3bigk with h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h0, hlam, p713_1]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h439, hlam, p713_1]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h628, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h439, h703, h704, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p713_1, u5ehi8]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h704, hc03, hc34, hlam, hphi, p713_1]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h704, hc23, hc34, hlam, hphi, p713_1]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h704, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h704, h712, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p713_1, u4ehi4]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h701, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p713_1, u4ehi4]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h703, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h708, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h703, h704, h712, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p713_1, u4ehi4]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h701, h712, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p713_1, u4ehi4]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p713_1]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h439, h701, h712, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p713_1, u4ehi4]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              rcases p713_3 (m.d 0 3) (by simp) with h733 | h733
                              · linarith only [h628, h733, hlam]
                              · linarith only [h701, h733, hlam]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h701, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h706, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h710, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [h712, hlam, p713_0]
                            · obtain ⟨p713_0, p713_1, p713_2, p713_3⟩ := h713c
                              linarith only [hlam, p713_0]
                          · linarith only [h712, hlam, hphi, ht45, u4ehi3, u5elo4]
                        · linarith only [h702, h711, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h439, h701, h710, hlam]
                  · linarith only [h702, h707, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h439, h701, h703, h706, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h746 | h746
              · linarith only [h628, h701, h746, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h748 | h748
                · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
                    · linarith only [h0, h746, h750, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h752 | h752
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                          · rcases h3bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h0, hlam, p755_1]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h439, hlam, p755_1]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h628, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h0, h703, h750, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u4ehi4]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h703, h750, hc03, hc34, hlam, hphi, p755_1]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h703, hlam, p755_1]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h746, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h703, h750, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u4ehi4]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h701, h750, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u4ehi4]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h750, hc13, hc34, hlam, hphi, p755_1]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h750, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h750, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u4ehi4]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h701, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u4ehi4]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h0, h701, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u4ehi4]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h703, hc12, hc34, hlam, hphi, ht23, p755_1]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              rcases p755_3 (m.d 0 3) (by simp) with h775 | h775
                              · linarith only [h628, h775, hlam]
                              · linarith only [h701, h775, hlam]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h701, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h748, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h752, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [h754, hlam, p755_0]
                            · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                              linarith only [hlam, p755_0]
                          · linarith only [h746, h754, hlam, hphi, ht45, u4ehi1, u5elo4]
                        · linarith only [h702, h753, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h0, h701, h703, h752, hlam]
                  · linarith only [h702, h749, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h0, h701, h748, hlam]
          · linarith only [h702, hlam, hphi, ht45, u4ehi0, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h789 | h789
          · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
            · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
              · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
                · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
                    · linarith only [h0, h628, h701, h789, h790, h792, h794, hc01, hc12, hlam, hphi, u5ehi9, u5elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h796 | h796
                      · linarith only [h0, h701, h791, h794, h796, hc01, hc14, hlam, hphi]
                      · linarith only [h439, h792, h796, hc02, hlam, hphi, ht23, ht34, ht45, u5elo1]
                  · linarith only [h789, h793, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h628, h791, h792, hlam, hphi, ht45, u4ehi0, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h801 | h801
                · linarith only [h0, h701, h791, h801, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h801, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h804 | h804
              · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                · rcases m.htr 1 4 5 (by decide) (by decide) with h806 | h806
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h807 | h807
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h808 | h808
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h809 | h809
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h810 | h810
                          · rcases h3bigk with h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, hlam, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h439, hlam, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h628, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h701, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              rcases p811_3 (m.d 0 3) (by simp) with h817 | h817
                              · linarith only [h0, h817, hlam]
                              · rcases p811_3 (m.d 1 3) (by simp) with h819 | h819
                                · rcases p811_3 (m.d 2 3) (by simp) with h820 | h820
                                  · rcases p811_3 (m.d 3 4) (by simp) with h821 | h821
                                    · linarith only [h804, h821, hlam]
                                    · linarith only [h628, h821, hlam]
                                  · linarith only [h439, h820, hlam]
                                · linarith only [h0, h819, hlam]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h790, hlam, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h628, h789, h790, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p811_1, u4ehi4]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, h701, h790, hc01, hc23, hlam, hphi, ht12, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              rcases p811_3 (m.d 0 3) (by simp) with h830 | h830
                              · linarith only [h439, h830, hlam]
                              · rcases p811_3 (m.d 1 3) (by simp) with h832 | h832
                                · linarith only [h790, h832, hlam]
                                · linarith only [h0, h832, hlam]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, h628, h701, h789, h805, hc01, hc23, hlam, hphi, ht12, ht45, p811_1, u4ehi4, u5elo1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, h701, hc01, hc23, hlam, hphi, ht12, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, h804, hc01, hc13, hlam, hphi, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h804, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h807, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, h701, h790, h804, hc01, hc23, hlam, hphi, ht12, p811_1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h0, h805, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p811_1, u5elo1]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h805, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h808, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [h810, hlam, p811_0]
                            · obtain ⟨p811_0, p811_1, p811_2, p811_3⟩ := h811c
                              linarith only [hlam, p811_0]
                          · linarith only [h628, h789, h810, hlam]
                        · linarith only [h628, h789, h807, h809, hlam]
                      · linarith only [h628, h789, h790, h804, h805, h808, hlam, hphi, ht45, u4ehi4, u5elo1]
                    · linarith only [h790, h804, h807, hlam]
                  · linarith only [h628, h789, h804, h806, hlam]
                · linarith only [h628, h789, h804, h805, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h855 | h855
                · linarith only [h0, h701, h804, h855, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h855, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h789, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB3_M_LI_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5bigk := hb5.1
  have h3ehi := hb3.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h13, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h12, h6, hc14, hlam, hphi, u4elo0]
                        · linarith only [h10, h11, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h10, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h3, h6, h7, h9, hlam, hphi, ht34, u3ehi2, u4elo0]
                  · linarith only [h7, h8, hlam, hphi, ht34, u3ehi2, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                  · rcases h4bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h22, h25, h27, hlam, hphi, ht34, p30_1, u3ehi4, u4elo0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h27, h28, hlam, hphi, ht34, p30_1, u3ehi4, u4elo0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h29, hlam, hphi, ht34, p30_1, u3ehi4, u4elo0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      rcases p30_3 (m.d 0 4) (by simp) with h35 | h35
                                      · rcases p30_3 (m.d 1 4) (by simp) with h36 | h36
                                        · rcases p30_3 (m.d 2 4) (by simp) with h37 | h37
                                          · linarith only [h2, h37, hlam]
                                          · linarith only [h28, h37, hlam]
                                        · linarith only [h25, h36, hlam]
                                      · linarith only [h35, hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [hc04, hlam, hphi, p30_1, u4elo1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h27, h28, hlam, hphi, ht34, p30_1, u3ehi4, u4elo1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h29, hlam, hphi, ht34, p30_1, u3ehi4, u4elo1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      rcases p30_3 (m.d 0 4) (by simp) with h46 | h46
                                      · rcases p30_3 (m.d 1 4) (by simp) with h47 | h47
                                        · rcases p30_3 (m.d 2 4) (by simp) with h48 | h48
                                          · linarith only [h21, h48, hlam]
                                          · linarith only [h28, h48, hlam]
                                        · linarith only [h47, hlam, p30_0]
                                      · linarith only [h46, h6, hlam]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h2, hlam, p30_1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h21, hlam, p30_1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h21, h29, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30_1, u3ehi4]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h21, h7, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30_1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h4, hlam, p30_1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h23, hlam, p30_1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h26, hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h21, h26, h7, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30_1]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h6, hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h25, hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h28, hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [h29, hlam, p30_0]
                                    · obtain ⟨p30_0, p30_1, p30_2, p30_3⟩ := h30c
                                      linarith only [hlam, p30_0]
                                  · linarith only [h29, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h28, h6, hc24, hlam, hphi, u4elo0]
                              · linarith only [h27, h5, h6, h7, hc12, hlam, hphi, ht23, ht34, u4elo0]
                            · linarith only [h21, h23, h24, h25, h26, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h23, h25, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h24, h5, h6, hlam, hphi, ht34, u3ehi1, u4elo0]
                      · linarith only [h23, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h21, h22, h3, h6, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h2, h21, h76, h78, hlam, hphi, ht34, u3ehi4, u4elo0]
                        · linarith only [h77, h78, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h77, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                                  · rcases h4bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hc14, hlam, hphi, p89_1, u4elo0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hc24, hlam, hphi, p89_1, u4elo0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hlam, hphi, ht34, p89_1, u3ehi3, u4elo0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      rcases p89_3 (m.d 0 4) (by simp) with h94 | h94
                                      · rcases p89_3 (m.d 1 4) (by simp) with h95 | h95
                                        · linarith only [h2, h21, h95, hlam]
                                        · linarith only [h84, h95, hlam]
                                      · linarith only [h94, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h2, h21, hlam, p89_1]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h21, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h2, h21, h88, hlam, hphi, ht34, p89_1, u3ehi4, u4elo0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      rcases p89_3 (m.d 0 4) (by simp) with h103 | h103
                                      · rcases p89_3 (m.d 1 4) (by simp) with h104 | h104
                                        · rcases p89_3 (m.d 2 4) (by simp) with h105 | h105
                                          · rcases p89_3 (m.d 3 4) (by simp) with h106 | h106
                                            · linarith only [h106, h82, hlam]
                                            · linarith only [h106, h88, hlam]
                                          · linarith only [h105, h87, hlam]
                                        · linarith only [h104, hlam, p89_0]
                                      · linarith only [h103, h6, hlam]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h2, hlam, p89_1]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h2, hc14, hlam, hphi, p89_1, u4elo0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h2, h88, hlam, hphi, ht34, p89_1, u3ehi4, u4elo0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      rcases p89_3 (m.d 0 4) (by simp) with h116 | h116
                                      · rcases p89_3 (m.d 1 4) (by simp) with h117 | h117
                                        · linarith only [h117, h21, hlam]
                                        · linarith only [h117, h84, hlam]
                                      · linarith only [h116, h6, hlam]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h4, hlam, p89_1]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h82, hlam, p89_1]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h85, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      rcases p89_3 (m.d 0 4) (by simp) with h125 | h125
                                      · rcases p89_3 (m.d 1 4) (by simp) with h126 | h126
                                        · rcases p89_3 (m.d 2 4) (by simp) with h127 | h127
                                          · rcases p89_3 (m.d 3 4) (by simp) with h128 | h128
                                            · rcases p89_3 (m.d 4 5) (by simp) with h129 | h129
                                              · linarith only [h129, hlam, p89_0]
                                              · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h83, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1, u3ehi4]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h0, h3, h76, h82, h83, hc01, hc45, hlam, hphi, ht0b, ht34, ht5b, p131_1, p89_1, u3ehi4, u4elo1]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h0, h3, h82, hc01, hc45, hlam, hphi, ht0b, ht34, ht5b, p131_1, p89_1, u3ehi4, u4elo1]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p131_1, u4elo0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h1, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h76, hlam, p131_1]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p131_1, u3ehi4]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h3, h6, h76, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p131_1, u4elo0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h3, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h3, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p131_1, u4elo0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h3, h6, hlam, hphi, ht34, p131_1, u3ehi4, u4elo0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h3, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p131_1, u4elo0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h5, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h83, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h86, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h1, h83, hc01, hc45, hlam, hphi, ht0b, ht5b, p131_1]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h6, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h84, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h87, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [h88, hlam, p131_0]
                                                · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                                  linarith only [hlam, p131_0]
                                            · linarith only [h128, hlam, p89_0]
                                          · linarith only [h127, h87, hlam]
                                        · linarith only [h126, h84, hlam]
                                      · linarith only [h125, h6, hlam]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h6, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h84, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h87, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [h88, hlam, p89_0]
                                    · obtain ⟨p89_0, p89_1, p89_2, p89_3⟩ := h89c
                                      linarith only [hlam, p89_0]
                                  · linarith only [h88, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h21, h84, h87, hlam]
                              · linarith only [h3, h6, h76, h83, h86, hlam, hphi, ht34, u3ehi2, u4elo0]
                            · linarith only [h7, h85, hlam, hphi, ht34, u3ehi1, u4elo3]
                          · linarith only [h6, h84, hc14, hlam, hphi, u4elo0]
                        · linarith only [h82, h83, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h82, hlam, hphi, ht34, u3ehi1, u4elo3]
              · linarith only [h4, h6, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
          · linarith only [h4, hlam, hphi, ht34, u3ehi0, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
          · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
            · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
              · linarith only [h178, h2, h3, hlam]
              · linarith only [h176, h178, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h176, h177, hc35, hlam, hphi, u3ehi3]
          · linarith only [h176, hlam, hphi, ht34, u3ehi0, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
        · rcases m.htr 0 3 4 (by decide) (by decide) with h184 | h184
          · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
            · linarith only [h183, h185, h2, hlam, hphi, ht34, u3ehi4, u4elo2]
            · linarith only [h184, h185, hc35, hlam, hphi, u3ehi3]
          · linarith only [h184, hlam, hphi, ht34, u3ehi0, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
          · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
            · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                · linarith only [h0, h192, h2, hlam, hphi, ht34, u3ehi2, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                  · linarith only [h0, h194, h2, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                    · linarith only [h0, h183, h196, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                                  · rcases h4bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h2, hc14, hlam, hphi, p205_1, u4elo2]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h2, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h2, hlam, hphi, ht34, p205_1, u3ehi3, u4elo2]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      rcases p205_3 (m.d 0 4) (by simp) with h210 | h210
                                      · rcases p205_3 (m.d 1 4) (by simp) with h211 | h211
                                        · rcases p205_3 (m.d 2 4) (by simp) with h212 | h212
                                          · rcases p205_3 (m.d 3 4) (by simp) with h213 | h213
                                            · linarith only [h189, h213, hlam]
                                            · linarith only [h204, h213, hlam]
                                          · linarith only [h203, h212, hlam]
                                        · linarith only [h200, h211, hlam]
                                      · linarith only [h210, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hc04, hlam, hphi, p205_1, u4elo1]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h194, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h204, hlam, hphi, ht34, p205_1, u3ehi4, u4elo1]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      rcases p205_3 (m.d 0 4) (by simp) with h223 | h223
                                      · rcases p205_3 (m.d 1 4) (by simp) with h224 | h224
                                        · rcases p205_3 (m.d 2 4) (by simp) with h225 | h225
                                          · rcases p205_3 (m.d 3 4) (by simp) with h226 | h226
                                            · linarith only [h198, h226, hlam]
                                            · linarith only [h204, h226, hlam]
                                          · linarith only [h203, h225, hlam]
                                        · linarith only [h224, hlam, p205_0]
                                      · linarith only [h191, h223, hlam]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hc04, hlam, hphi, p205_1, u4elo2]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hc14, hlam, hphi, p205_1, u4elo2]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h204, hlam, hphi, ht34, p205_1, u3ehi4, u4elo2]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      rcases p205_3 (m.d 0 4) (by simp) with h236 | h236
                                      · linarith only [h2, h236, hlam]
                                      · linarith only [h191, h236, hlam]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h189, hlam, p205_1]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h198, hlam, p205_1]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h201, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      rcases p205_3 (m.d 0 4) (by simp) with h243 | h243
                                      · rcases p205_3 (m.d 1 4) (by simp) with h244 | h244
                                        · rcases p205_3 (m.d 2 4) (by simp) with h245 | h245
                                          · rcases p205_3 (m.d 3 4) (by simp) with h246 | h246
                                            · rcases p205_3 (m.d 4 5) (by simp) with h247 | h247
                                              · linarith only [h247, hlam, p205_0]
                                              · rcases h5bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h199, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1, u3ehi4]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h183, hlam, p249_1]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h183, h203, hlam, hphi, ht34, p249_1, u3ehi4, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h183, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h1, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h196, hlam, p249_1]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p249_1, u3ehi4]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h1, h183, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h203, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h203, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h203, hlam, hphi, ht34, p249_1, u3ehi4, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p249_1, u4elo2]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h190, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h199, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h202, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h1, h199, hc01, hc45, hlam, hphi, ht0b, ht5b, p249_1]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h191, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h200, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h203, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [h204, hlam, p249_0]
                                                · obtain ⟨p249_0, p249_1, p249_2, p249_3⟩ := h249c
                                                  linarith only [hlam, p249_0]
                                            · linarith only [h246, hlam, p205_0]
                                          · linarith only [h203, h245, hlam]
                                        · linarith only [h200, h244, hlam]
                                      · linarith only [h191, h243, hlam]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h191, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h200, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h203, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [h204, hlam, p205_0]
                                    · obtain ⟨p205_0, p205_1, p205_2, p205_3⟩ := h205c
                                      linarith only [hlam, p205_0]
                                  · linarith only [h204, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h0, h2, h203, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h192, h198, h199, h202, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h192, h198, h201, hlam]
                          · linarith only [h191, h2, h200, hc14, hlam, hphi, u4elo2]
                        · linarith only [h190, h198, h199, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h198, hlam, hphi, ht34, u3ehi1, u4elo3]
              · linarith only [h189, h191, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h189, h190, hc35, hlam, hphi, u3ehi3]
          · linarith only [h189, hlam, hphi, ht34, u3ehi0, u4elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h294 | h294
      · rcases m.htr 0 2 5 (by decide) (by decide) with h295 | h295
        · linarith only [h0, h1, h295, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
          · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
            · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
              · linarith only [h0, h1, h294, h299, hlam]
              · linarith only [h297, h299, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h297, h298, hc35, hlam, hphi, u3ehi3]
          · linarith only [h297, hlam, hphi, ht34, u3ehi0, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h304 | h304
        · linarith only [h0, h1, h294, h304, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
          · rcases m.htr 0 3 5 (by decide) (by decide) with h307 | h307
            · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
              · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
                · linarith only [h0, h294, h309, hlam, hphi, ht34, u3ehi2, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h311 | h311
                  · linarith only [h0, h1, h294, h308, h311, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h313 | h313
                    · linarith only [h0, h1, h294, h304, h308, h313, hc02, hlam, hphi, ht23, ht34, u4elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h315 | h315
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h316 | h316
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h317 | h317
                          · linarith only [h0, h1, h317, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · linarith only [h294, h308, h317, hc14, hlam, hphi, u4elo2]
                        · linarith only [h294, h307, h308, h316, hlam, hphi, ht34, u3ehi1, u4elo2]
                      · linarith only [h315, hlam, hphi, ht34, u3ehi1, u4elo3]
              · linarith only [h306, h308, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h306, h307, hc35, hlam, hphi, u3ehi3]
          · linarith only [h306, hlam, hphi, ht34, u3ehi0, u4elo3]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
    · rcases m.htr 0 2 4 (by decide) (by decide) with h326 | h326
      · rcases m.htr 0 2 5 (by decide) (by decide) with h327 | h327
        · rcases m.htr 0 3 4 (by decide) (by decide) with h328 | h328
          · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
            · rcases m.htr 0 4 5 (by decide) (by decide) with h330 | h330
              · rcases m.htr 1 2 3 (by decide) (by decide) with h331 | h331
                · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                                  · rcases h4bigk with h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hc14, hlam, hphi, p341_1, u4elo0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hc24, hlam, hphi, p341_1, u4elo0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hlam, hphi, ht34, p341_1, u3ehi3, u4elo0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      rcases p341_3 (m.d 0 4) (by simp) with h346 | h346
                                      · rcases p341_3 (m.d 1 4) (by simp) with h347 | h347
                                        · rcases p341_3 (m.d 2 4) (by simp) with h348 | h348
                                          · linarith only [h326, h348, hlam]
                                          · linarith only [h339, h348, hlam]
                                        · linarith only [h336, h347, hlam]
                                      · linarith only [h346, hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hc04, hlam, hphi, p341_1, u4elo1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h338, h339, hlam, hphi, ht34, p341_1, u3ehi4, u4elo1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h340, hlam, hphi, ht34, p341_1, u3ehi4, u4elo1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      rcases p341_3 (m.d 0 4) (by simp) with h357 | h357
                                      · rcases p341_3 (m.d 1 4) (by simp) with h358 | h358
                                        · rcases p341_3 (m.d 2 4) (by simp) with h359 | h359
                                          · linarith only [h332, h359, hlam]
                                          · linarith only [h339, h359, hlam]
                                        · linarith only [h358, hlam, p341_0]
                                      · linarith only [h330, h357, hlam]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h326, hlam, p341_1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h332, hlam, p341_1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h340, hlam, hphi, ht34, p341_1, u3ehi4, u4elo2]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      rcases p341_3 (m.d 0 4) (by simp) with h368 | h368
                                      · rcases p341_3 (m.d 1 4) (by simp) with h369 | h369
                                        · rcases p341_3 (m.d 2 4) (by simp) with h370 | h370
                                          · rcases p341_3 (m.d 3 4) (by simp) with h371 | h371
                                            · linarith only [h337, h371, hlam]
                                            · linarith only [h340, h371, hlam]
                                          · linarith only [h370, hlam, p341_0]
                                        · linarith only [h336, h369, hlam]
                                      · linarith only [h330, h368, hlam]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h328, hlam, p341_1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h334, hlam, p341_1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h337, hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h331, h337, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p341_1]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h330, hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h336, hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h339, hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [h340, hlam, p341_0]
                                    · obtain ⟨p341_0, p341_1, p341_2, p341_3⟩ := h341c
                                      linarith only [hlam, p341_0]
                                  · linarith only [h340, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h330, h339, hc24, hlam, hphi, u4elo0]
                              · linarith only [h329, h330, h338, hlam, hphi, ht34, u3ehi2, u4elo0]
                            · linarith only [h337, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h330, h336, hc14, hlam, hphi, u4elo0]
                        · linarith only [h329, h330, h335, hlam, hphi, ht34, u3ehi1, u4elo0]
                      · linarith only [h328, h331, h334, hlam, hphi, ht34, u3ehi2, u4elo0]
                    · linarith only [h0, h325, h327, h333, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h325, h329, h332, hlam, hphi, ht34, u3ehi4, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                        · linarith only [h0, h325, h331, h399, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h398, h399, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h331, h398, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h327, h397, hlam]
                  · linarith only [h0, h326, h396, hlam]
              · linarith only [h328, h330, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h328, h329, hc35, hlam, hphi, u3ehi3]
          · linarith only [h328, hlam, hphi, ht34, u3ehi0, u4elo3]
        · linarith only [h0, h325, h327, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h409 | h409
        · rcases m.htr 0 3 4 (by decide) (by decide) with h410 | h410
          · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
            · linarith only [h0, h325, h326, h411, hlam, hphi, ht34, u3ehi4, u4elo2]
            · linarith only [h410, h411, hc35, hlam, hphi, u3ehi3]
          · linarith only [h410, hlam, hphi, ht34, u3ehi0, u4elo3]
        · linarith only [h0, h325, h409, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h416 | h416
      · rcases m.htr 0 2 5 (by decide) (by decide) with h417 | h417
        · rcases m.htr 0 3 4 (by decide) (by decide) with h418 | h418
          · rcases m.htr 0 3 5 (by decide) (by decide) with h419 | h419
            · rcases m.htr 0 4 5 (by decide) (by decide) with h420 | h420
              · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h424 | h424
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h425 | h425
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h426 | h426
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h428 | h428
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h429 | h429
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
                                  · rcases h4bigk with h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h325, h426, hc01, hlam, hphi, ht12, ht23, ht34, p431_1, u4elo0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hc24, hlam, hphi, p431_1, u4elo0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hc34, hlam, hphi, p431_1, u4elo0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      rcases p431_3 (m.d 0 4) (by simp) with h436 | h436
                                      · rcases p431_3 (m.d 1 4) (by simp) with h437 | h437
                                        · rcases p431_3 (m.d 2 4) (by simp) with h438 | h438
                                          · linarith only [h416, h438, hlam]
                                          · linarith only [h429, h438, hlam]
                                        · linarith only [h426, h437, hlam]
                                      · linarith only [h436, hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hc04, hlam, hphi, p431_1, u4elo1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h427, h430, hlam, hphi, ht34, p431_1, u3ehi4, u4elo1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h430, hlam, hphi, ht34, p431_1, u3ehi4, u4elo1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      rcases p431_3 (m.d 0 4) (by simp) with h447 | h447
                                      · rcases p431_3 (m.d 1 4) (by simp) with h448 | h448
                                        · rcases p431_3 (m.d 2 4) (by simp) with h449 | h449
                                          · linarith only [h422, h449, hlam]
                                          · linarith only [h429, h449, hlam]
                                        · linarith only [h448, hlam, p431_0]
                                      · linarith only [h420, h447, hlam]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h416, hlam, p431_1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h422, hlam, p431_1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h430, hlam, hphi, ht34, p431_1, u3ehi4, u4elo2]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      rcases p431_3 (m.d 0 4) (by simp) with h458 | h458
                                      · rcases p431_3 (m.d 1 4) (by simp) with h459 | h459
                                        · rcases p431_3 (m.d 2 4) (by simp) with h460 | h460
                                          · rcases p431_3 (m.d 3 4) (by simp) with h461 | h461
                                            · linarith only [h427, h461, hlam]
                                            · linarith only [h430, h461, hlam]
                                          · linarith only [h460, hlam, p431_0]
                                        · linarith only [h426, h459, hlam]
                                      · linarith only [h420, h458, hlam]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h418, hlam, p431_1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h424, hlam, p431_1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h427, hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h421, h427, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p431_1]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h420, hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h426, hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h429, hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [h430, hlam, p431_0]
                                    · obtain ⟨p431_0, p431_1, p431_2, p431_3⟩ := h431c
                                      linarith only [hlam, p431_0]
                                  · linarith only [h430, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h420, h429, hc24, hlam, hphi, u4elo0]
                              · linarith only [h325, h419, h426, h428, hlam, hphi, ht34, u3ehi2, u4elo1]
                            · linarith only [h427, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h420, h426, hc14, hlam, hphi, u4elo0]
                        · linarith only [h419, h420, h425, hlam, hphi, ht34, u3ehi1, u4elo0]
                      · linarith only [h418, h421, h424, hlam, hphi, ht34, u3ehi2, u4elo0]
                    · linarith only [h0, h417, h420, h423, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                  · linarith only [h0, h416, h422, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h486 | h486
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h492 | h492
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h493 | h493
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h494 | h494
                                  · rcases h4bigk with h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hc14, hlam, hphi, p495_1, u4elo0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h492, h493, hlam, hphi, ht34, p495_1, u3ehi4, u4elo0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h494, hlam, hphi, ht34, p495_1, u3ehi4, u4elo0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      rcases p495_3 (m.d 0 4) (by simp) with h500 | h500
                                      · rcases p495_3 (m.d 1 4) (by simp) with h501 | h501
                                        · rcases p495_3 (m.d 2 4) (by simp) with h502 | h502
                                          · linarith only [h416, h502, hlam]
                                          · linarith only [h493, h502, hlam]
                                        · linarith only [h490, h501, hlam]
                                      · linarith only [h500, hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hc04, hlam, hphi, p495_1, u4elo1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h492, h493, hlam, hphi, ht34, p495_1, u3ehi4, u4elo1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h494, hlam, hphi, ht34, p495_1, u3ehi4, u4elo1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      rcases p495_3 (m.d 0 4) (by simp) with h511 | h511
                                      · rcases p495_3 (m.d 1 4) (by simp) with h512 | h512
                                        · rcases p495_3 (m.d 2 4) (by simp) with h513 | h513
                                          · linarith only [h486, h513, hlam]
                                          · linarith only [h493, h513, hlam]
                                        · linarith only [h512, hlam, p495_0]
                                      · linarith only [h420, h511, hlam]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h416, hlam, p495_1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h486, hlam, p495_1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h0, h416, h421, h494, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p495_1, u3ehi4]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h0, h416, h421, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p495_1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h418, hlam, p495_1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h488, hlam, p495_1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h491, hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h0, h416, h421, h491, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p495_1]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h420, hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h490, hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h493, hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [h494, hlam, p495_0]
                                    · obtain ⟨p495_0, p495_1, p495_2, p495_3⟩ := h495c
                                      linarith only [hlam, p495_0]
                                  · linarith only [h494, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h490, h493, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h421, h492, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h421, h491, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h420, h490, hc14, hlam, hphi, u4elo0]
                        · linarith only [h419, h420, h489, hlam, hphi, ht34, u3ehi1, u4elo0]
                      · linarith only [h0, h416, h418, h421, h488, hlam]
                    · linarith only [h0, h417, h487, hlam]
                  · linarith only [h0, h416, h418, h486, hlam, hphi, ht34, u3ehi3, u4elo2]
              · linarith only [h418, h420, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h418, h419, hc35, hlam, hphi, u3ehi3]
          · linarith only [h418, hlam, hphi, ht34, u3ehi0, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h545 | h545
          · rcases m.htr 0 3 5 (by decide) (by decide) with h546 | h546
            · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
              · linarith only [h416, h417, h547, hlam]
              · linarith only [h545, h547, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h545, h546, hc35, hlam, hphi, u3ehi3]
          · linarith only [h545, hlam, hphi, ht34, u3ehi0, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h552 | h552
        · rcases m.htr 0 3 4 (by decide) (by decide) with h553 | h553
          · rcases m.htr 0 3 5 (by decide) (by decide) with h554 | h554
            · linarith only [h416, h552, h554, hlam, hphi, ht34, u3ehi4, u4elo2]
            · linarith only [h553, h554, hc35, hlam, hphi, u3ehi3]
          · linarith only [h553, hlam, hphi, ht34, u3ehi0, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h558 | h558
          · rcases m.htr 0 3 5 (by decide) (by decide) with h559 | h559
            · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
              · rcases m.htr 1 2 3 (by decide) (by decide) with h561 | h561
                · rcases m.htr 1 2 4 (by decide) (by decide) with h562 | h562
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h563 | h563
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h564 | h564
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                  · rcases h4bigk with h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h416, h562, hlam, p571_1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h416, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h416, h562, hc34, hlam, hphi, p571_1, u4elo1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      rcases p571_3 (m.d 0 4) (by simp) with h576 | h576
                                      · rcases p571_3 (m.d 1 4) (by simp) with h577 | h577
                                        · rcases p571_3 (m.d 2 4) (by simp) with h578 | h578
                                          · rcases p571_3 (m.d 3 4) (by simp) with h579 | h579
                                            · linarith only [h558, h579, hlam]
                                            · linarith only [h570, h579, hlam]
                                          · linarith only [h569, h578, hlam]
                                        · linarith only [h566, h577, hlam]
                                      · linarith only [h576, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hc04, hlam, hphi, p571_1, u4elo1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hc24, hlam, hphi, p571_1, u4elo1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h570, hlam, hphi, ht34, p571_1, u3ehi4, u4elo1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      rcases p571_3 (m.d 0 4) (by simp) with h589 | h589
                                      · linarith only [h416, h562, h589, hlam]
                                      · linarith only [h560, h589, hlam]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hc04, hlam, hphi, p571_1, u4elo2]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h562, hlam, p571_1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h562, h570, hlam, hphi, ht34, p571_1, u3ehi4, u4elo1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      rcases p571_3 (m.d 0 4) (by simp) with h596 | h596
                                      · linarith only [h416, h596, hlam]
                                      · linarith only [h560, h596, hlam]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h558, hlam, p571_1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h564, hlam, p571_1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h567, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h561, h567, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p571_1]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h560, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h566, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h569, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [h570, hlam, p571_0]
                                    · obtain ⟨p571_0, p571_1, p571_2, p571_3⟩ := h571c
                                      linarith only [hlam, p571_0]
                                  · linarith only [h570, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h416, h560, h569, hlam]
                              · linarith only [h325, h559, h566, h568, hlam, hphi, ht34, u3ehi2, u4elo1]
                            · linarith only [h567, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h416, h560, h562, h566, hlam]
                        · linarith only [h564, h565, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h564, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h0, h416, h562, h563, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h562, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h618 | h618
                  · linarith only [h0, h416, h561, h618, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h618, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h558, h560, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h558, h559, hc35, hlam, hphi, u3ehi3]
          · linarith only [h558, hlam, hphi, ht34, u3ehi0, u4elo3]

theorem n7l_sAB3_M_LI_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
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
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h18, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h17, h9, hc24, hlam, hphi, u4elo0]
                                  · linarith only [h16, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                                  · linarith only [h0, h10, h13, h15, h23, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h23, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h14, h8, hc13, hlam, hphi, ht34, ht45, u5elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                                · linarith only [h10, h13, h28, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                                      · rcases h3bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          rcases p33_3 (m.d 0 3) (by simp) with h35 | h35
                                          · rcases p33_3 (m.d 1 3) (by simp) with h36 | h36
                                            · linarith only [h1, h36, hlam]
                                            · rcases p33_3 (m.d 2 3) (by simp) with h38 | h38
                                              · linarith only [h38, h4, hlam]
                                              · rcases p33_3 (m.d 3 4) (by simp) with h40 | h40
                                                · linarith only [h40, h7, hlam]
                                                · linarith only [h13, h40, hlam]
                                          · linarith only [h1, h35, hlam]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          rcases p33_3 (m.d 0 3) (by simp) with h44 | h44
                                          · rcases p33_3 (m.d 1 3) (by simp) with h45 | h45
                                            · linarith only [h1, h45, hlam]
                                            · linarith only [h10, h45, hlam]
                                          · linarith only [h4, h44, hlam]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h0, h10, h13, h30, h32, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p33_1]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h10, h13, h30, h7, hlam, p33_2]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h1, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h13, h30, h32, h7, hc04, hc45, hlam, hphi, ht0b, ht5b, p33_1]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h13, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h13, h32, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p33_1, u4elo0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h4, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h10, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h28, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h0, h10, h32, hc01, hc45, hlam, hphi, ht0b, ht5b, p33_1]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h7, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h7, hc13, hlam, hphi, ht34, p33_1, u4elo0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h7, hc23, hlam, hphi, ht34, p33_1, u4elo0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          rcases p33_3 (m.d 0 3) (by simp) with h65 | h65
                                          · rcases p33_3 (m.d 1 3) (by simp) with h66 | h66
                                            · linarith only [h13, h66, hlam]
                                            · linarith only [h27, h66, hlam]
                                          · linarith only [h65, h8, hlam]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h8, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h27, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h30, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [h32, hlam, p33_0]
                                        · obtain ⟨p33_0, p33_1, p33_2, p33_3⟩ := h33c
                                          linarith only [hlam, p33_0]
                                      · linarith only [h13, h32, hc13, hlam, hphi, ht34, u4elo4]
                                    · linarith only [h31, h9, hc24, hlam, hphi, ht45, u5elo0]
                                  · linarith only [h30, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h27, h8, hc13, hlam, hphi, ht34, ht45, u5elo0]
                          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                                    · linarith only [h0, h10, h4, h81, h87, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h87, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h10, h86, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h10, h81, h85, hc24, hlam, hphi, u4elo3]
                              · linarith only [h10, h81, h84, hc24, hlam, hphi, ht45, u5elo3]
                            · linarith only [h10, h81, h83, hc24, hlam, hphi, u4elo3]
                          · linarith only [h81, h82, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h100 | h100
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                                      · rcases h3bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h101, h96, hc03, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h0, h101, h4, h81, h95, h98, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          rcases p102_3 (m.d 0 3) (by simp) with h106 | h106
                                          · rcases p102_3 (m.d 1 3) (by simp) with h107 | h107
                                            · linarith only [h1, h107, hlam]
                                            · linarith only [h107, h96, hlam]
                                          · linarith only [h106, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          rcases p102_3 (m.d 0 3) (by simp) with h111 | h111
                                          · rcases p102_3 (m.d 1 3) (by simp) with h112 | h112
                                            · linarith only [h1, h112, hlam]
                                            · linarith only [h112, h97, hlam]
                                          · linarith only [h111, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h1, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h10, hlam, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h1, h101, hc01, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          rcases p102_3 (m.d 0 3) (by simp) with h120 | h120
                                          · rcases p102_3 (m.d 1 3) (by simp) with h121 | h121
                                            · rcases p102_3 (m.d 2 3) (by simp) with h122 | h122
                                              · rcases p102_3 (m.d 3 4) (by simp) with h123 | h123
                                                · linarith only [h123, h96, hlam]
                                                · linarith only [h101, h123, hlam]
                                              · linarith only [h122, h99, hlam]
                                            · linarith only [h121, hlam, p102_0]
                                          · linarith only [h120, h8, hlam]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h4, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h0, h10, h101, h4, h95, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h0, h101, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          rcases p102_3 (m.d 0 3) (by simp) with h133 | h133
                                          · rcases p102_3 (m.d 1 3) (by simp) with h134 | h134
                                            · linarith only [h10, h134, hlam]
                                            · linarith only [h134, h97, hlam]
                                          · linarith only [h133, h8, hlam]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h7, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h96, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h98, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h1, h101, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h8, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h97, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h99, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [h101, hlam, p102_0]
                                        · obtain ⟨p102_0, p102_1, p102_2, p102_3⟩ := h102c
                                          linarith only [hlam, p102_0]
                                      · linarith only [h101, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h100, h81, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h10, h5, h81, h95, h99, hc13, hc25, hlam, hphi, ht34, u4elo0, u5elo3]
                                · linarith only [h10, h95, h96, h98, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h5, h8, h81, h95, h97, hc13, hc25, hlam, hphi, ht34, u4elo0, u5elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                                · linarith only [h0, h10, h154, h4, h95, h96, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                · linarith only [h10, h154, h7, h95, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                              · linarith only [h10, h153, h95, hc25, hlam, hphi, u5elo3]
                          · linarith only [h95, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                            · linarith only [h1, h166, h7, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                                · linarith only [h1, h163, h169, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                      · rcases h3bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h163, h171, h173, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p174_1]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h171, h173, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p174_1, u4elo0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h7, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h173, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p174_1, u4elo3]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h1, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h166, h171, h173, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p174_1, u4elo1]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h166, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h1, h173, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p174_1, u4elo3]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h4, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h163, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h169, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h0, h164, h169, h173, hc01, hc45, hlam, hphi, ht0b, ht5b, p174_1]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hc03, hlam, hphi, ht34, p174_1, u4elo3]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h163, hc23, hlam, hphi, ht34, p174_1, u4elo3]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hc23, hlam, hphi, ht34, p174_1, u4elo3]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          rcases p174_3 (m.d 0 3) (by simp) with h194 | h194
                                          · linarith only [h194, h7, hlam]
                                          · linarith only [h161, h194, hlam]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h161, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h168, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h171, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [h173, hlam, p174_0]
                                        · obtain ⟨p174_0, p174_1, p174_2, p174_3⟩ := h174c
                                          linarith only [hlam, p174_0]
                                      · linarith only [h173, h7, hc04, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h162, h172, hc24, hlam, hphi, u4elo0]
                                  · linarith only [h1, h168, h171, h7, hc23, hlam, hphi, ht34, u4elo3]
                              · linarith only [h168, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h165, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h163, h164, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h163, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h162, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h161, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h213 | h213
            · rcases m.htr 0 2 5 (by decide) (by decide) with h214 | h214
              · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
                · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                      · linarith only [h0, h213, h218, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h226 | h226
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h227 | h227
                                      · rcases h3bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h218, h220, h224, h227, hc03, hc45, hlam, hphi, ht0b, ht5b, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h4, hlam, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          rcases p228_3 (m.d 0 3) (by simp) with h232 | h232
                                          · rcases p228_3 (m.d 1 3) (by simp) with h233 | h233
                                            · linarith only [h1, h233, hlam]
                                            · linarith only [h222, h233, hlam]
                                          · linarith only [h232, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          rcases p228_3 (m.d 0 3) (by simp) with h237 | h237
                                          · rcases p228_3 (m.d 1 3) (by simp) with h238 | h238
                                            · linarith only [h1, h238, hlam]
                                            · linarith only [h223, h238, hlam]
                                          · linarith only [h237, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h1, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h218, hlam, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h1, h227, hc01, hc45, hlam, hphi, ht0b, ht5b, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          rcases p228_3 (m.d 0 3) (by simp) with h246 | h246
                                          · rcases p228_3 (m.d 1 3) (by simp) with h247 | h247
                                            · rcases p228_3 (m.d 2 3) (by simp) with h248 | h248
                                              · rcases p228_3 (m.d 3 4) (by simp) with h249 | h249
                                                · linarith only [h222, h249, hlam]
                                                · linarith only [h227, h249, hlam]
                                              · linarith only [h225, h248, hlam]
                                            · linarith only [h247, hlam, p228_0]
                                          · linarith only [h216, h246, hlam]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h0, h220, h224, h227, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h218, h220, h224, h227, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          rcases p228_3 (m.d 0 3) (by simp) with h258 | h258
                                          · linarith only [h258, h4, hlam]
                                          · linarith only [h215, h258, hlam]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          rcases p228_3 (m.d 0 3) (by simp) with h261 | h261
                                          · linarith only [h261, h4, hlam]
                                          · linarith only [h216, h261, hlam]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h215, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h222, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h224, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h0, h220, h224, hc01, hc35, hlam, hphi, ht0b, ht5b, p228_1]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h216, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h223, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h225, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [h227, hlam, p228_0]
                                        · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                                          linarith only [hlam, p228_0]
                                      · linarith only [h227, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h217, h226, hc24, hlam, hphi, u4elo0]
                                  · linarith only [h225, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h0, h220, h224, h4, hc24, hlam, hphi, u4elo3]
                              · linarith only [h223, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h218, h220, h222, hc24, hlam, hphi, u4elo3]
                          · linarith only [h220, h221, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h213, h220, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h217, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h213, h216, h4, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h213, h215, h4, hc24, hlam, hphi, u4elo3]
              · linarith only [h213, h214, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
              · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
                · rcases m.htr 0 3 5 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
                      · linarith only [h0, h286, h290, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                        · linarith only [h0, h213, h292, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h297 | h297
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h300 | h300
                                      · rcases h3bigk with h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h295, h300, hc03, hc45, hlam, hphi, ht0b, ht5b, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h4, hlam, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          rcases p301_3 (m.d 0 3) (by simp) with h305 | h305
                                          · rcases p301_3 (m.d 1 3) (by simp) with h306 | h306
                                            · linarith only [h1, h306, hlam]
                                            · linarith only [h295, h306, hlam]
                                          · linarith only [h305, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          rcases p301_3 (m.d 0 3) (by simp) with h310 | h310
                                          · rcases p301_3 (m.d 1 3) (by simp) with h311 | h311
                                            · linarith only [h1, h311, hlam]
                                            · linarith only [h296, h311, hlam]
                                          · linarith only [h310, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h1, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h290, hlam, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h1, h300, hc01, hc45, hlam, hphi, ht0b, ht5b, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          rcases p301_3 (m.d 0 3) (by simp) with h319 | h319
                                          · rcases p301_3 (m.d 1 3) (by simp) with h320 | h320
                                            · rcases p301_3 (m.d 2 3) (by simp) with h321 | h321
                                              · rcases p301_3 (m.d 3 4) (by simp) with h322 | h322
                                                · linarith only [h295, h322, hlam]
                                                · linarith only [h300, h322, hlam]
                                              · linarith only [h298, h321, hlam]
                                            · linarith only [h320, hlam, p301_0]
                                          · linarith only [h288, h319, hlam]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h287, h300, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h295, h300, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          rcases p301_3 (m.d 0 3) (by simp) with h331 | h331
                                          · linarith only [h331, h4, hlam]
                                          · linarith only [h287, h331, hlam]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          rcases p301_3 (m.d 0 3) (by simp) with h334 | h334
                                          · linarith only [h334, h4, hlam]
                                          · linarith only [h288, h334, hlam]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h287, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h295, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h297, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h1, h295, h300, hc01, hc45, hlam, hphi, ht0b, ht5b, p301_1]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h288, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h296, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h298, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [h300, hlam, p301_0]
                                        · obtain ⟨p301_0, p301_1, p301_2, p301_3⟩ := h301c
                                          linarith only [hlam, p301_0]
                                      · linarith only [h300, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h213, h289, h294, h298, h299, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h213, h294, h298, h4, hc03, hc25, hlam, hphi, ht34, u4elo2, u5elo3]
                                · linarith only [h0, h1, h294, h295, h297, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h288, h296, hc13, hlam, hphi, ht34, ht45, u5elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                                      · rcases h3bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          rcases p357_3 (m.d 0 3) (by simp) with h359 | h359
                                          · rcases p357_3 (m.d 1 3) (by simp) with h360 | h360
                                            · linarith only [h1, h360, hlam]
                                            · rcases p357_3 (m.d 2 3) (by simp) with h362 | h362
                                              · rcases p357_3 (m.d 3 4) (by simp) with h363 | h363
                                                · linarith only [h287, h363, hlam]
                                                · linarith only [h295, h363, hlam]
                                              · linarith only [h290, h362, hlam]
                                          · linarith only [h1, h359, hlam]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h4, hlam, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h290, h294, h295, h354, h356, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h287, h290, h294, h295, h354, hlam, p357_2]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h1, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h290, hlam, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h295, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h213, h287, h295, h356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p357_1, u4elo2]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h287, h295, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          rcases p357_3 (m.d 0 3) (by simp) with h377 | h377
                                          · linarith only [h377, h4, hlam]
                                          · linarith only [h1, h377, hlam]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h290, h294, h295, h354, h356, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h287, h290, h294, h295, h354, h4, hlam, p357_2]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h287, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h213, h287, h290, h294, h354, h356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p357_1, u4elo2]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h353, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          rcases p357_3 (m.d 0 3) (by simp) with h387 | h387
                                          · rcases p357_3 (m.d 1 3) (by simp) with h388 | h388
                                            · linarith only [h295, h388, hlam]
                                            · linarith only [h352, h388, hlam]
                                          · linarith only [h288, h387, hlam]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h288, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h352, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h354, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h356, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                      · linarith only [h295, h356, hc14, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h213, h289, h355, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h287, h290, h294, h295, h354, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h287, h353, h4, hlam]
                              · linarith only [h290, h294, h352, hc25, hlam, hphi, u5elo3]
                          · linarith only [h294, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h289, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h213, h287, h288, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
                      · linarith only [h0, h287, h4, h407, hc23, hlam, hphi, ht34, u4elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
                        · linarith only [h0, h287, h4, h409, hc24, hlam, hphi, u4elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                            · linarith only [h0, h1, h287, h4, h411, h412, hc01, hc25, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                                      · rcases h3bigk with h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h287, h415, hc13, hlam, hphi, ht34, p419_1, u4elo2]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h4, hlam, p419_1]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h287, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h287, h415, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p419_1, u4elo2]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h1, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h407, hlam, p419_1]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h412, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h1, h287, h415, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p419_1, u4elo2]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          rcases p419_3 (m.d 0 3) (by simp) with h430 | h430
                                          · linarith only [h4, h430, hlam]
                                          · rcases p419_3 (m.d 1 3) (by simp) with h432 | h432
                                            · linarith only [h407, h432, hlam]
                                            · rcases p419_3 (m.d 2 3) (by simp) with h434 | h434
                                              · rcases p419_3 (m.d 3 4) (by simp) with h435 | h435
                                                · linarith only [h415, h435, hlam]
                                                · linarith only [h287, h435, hlam]
                                              · linarith only [h4, h434, hlam]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          rcases p419_3 (m.d 0 3) (by simp) with h439 | h439
                                          · linarith only [h4, h439, hlam]
                                          · linarith only [h1, h439, hlam]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h287, h4, hc02, hc23, hlam, hphi, p419_1]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h0, h287, h4, h411, h415, h416, hlam, p419_2]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h0, h4, h411, h415, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p419_1, u4elo2]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h415, hc13, hlam, hphi, ht34, p419_1, u4elo2]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h415, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          rcases p419_3 (m.d 0 3) (by simp) with h449 | h449
                                          · linarith only [h287, h449, hlam]
                                          · linarith only [h405, h449, hlam]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h405, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h414, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h416, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [h418, hlam, p419_0]
                                        · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                          linarith only [hlam, p419_0]
                                      · linarith only [h418, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1, h287, h406, h407, h411, h415, h416, h417, hc35, hlam, hphi, u5elo0]
                                  · linarith only [h287, h415, h416, hc03, hc35, hlam, hphi]
                                · linarith only [h0, h4, h411, h415, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                              · linarith only [h407, h411, h414, hc25, hlam, hphi, u5elo3]
                          · linarith only [h411, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h286, h287, h4, h406, hc04, hc25, hlam, hphi, u4elo3, u5elo4]
                  · linarith only [h286, h4, h405, hc25, hlam, hphi, u5elo3]
              · linarith only [h286, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h1, h2, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h468 | h468
      · rcases m.htr 0 1 5 (by decide) (by decide) with h469 | h469
        · rcases m.htr 0 2 3 (by decide) (by decide) with h470 | h470
          · linarith only [h0, h1, h470, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h472 | h472
            · rcases m.htr 0 2 5 (by decide) (by decide) with h473 | h473
              · rcases m.htr 0 3 4 (by decide) (by decide) with h474 | h474
                · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h476 | h476
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                      · linarith only [h0, h1, h470, h477, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h484 | h484
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h485 | h485
                                    · linarith only [h0, h1, h477, h479, h485, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h485, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h1, h477, h484, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h477, h479, h483, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h1, h479, h482, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h479, h481, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h479, h480, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1, h472, h477, h479, hc12, hc23, hlam, hphi]
                    · linarith only [h476, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1, h475, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h474, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h473, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h498 | h498
              · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
                · rcases m.htr 0 3 5 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h501 | h501
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                      · linarith only [h0, h472, h502, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                        · linarith only [h0, h472, h504, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h507 | h507
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h509 | h509
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h510 | h510
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h511 | h511
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h512 | h512
                                      · rcases h3bigk with h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, hlam, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h470, hlam, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          rcases p513_3 (m.d 0 3) (by simp) with h517 | h517
                                          · rcases p513_3 (m.d 1 3) (by simp) with h518 | h518
                                            · rcases p513_3 (m.d 2 3) (by simp) with h519 | h519
                                              · rcases p513_3 (m.d 3 4) (by simp) with h520 | h520
                                                · linarith only [h520, hlam, p513_0]
                                                · rcases p513_3 (m.d 3 5) (by simp) with h522 | h522
                                                  · linarith only [h500, h522, hlam]
                                                  · rcases h3emin with h524 | h524 | h524 | h524 | h524
                                                    · rcases h4bigk with h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h504, hc12, hlam, hphi, ht23, ht34, p525_1, u4elo0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h472, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hc34, hlam, hphi, p525_1, u4elo0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        rcases p525_3 (m.d 0 4) (by simp) with h530 | h530
                                                        · rcases p525_3 (m.d 1 4) (by simp) with h531 | h531
                                                          · linarith only [h468, h531, hlam]
                                                          · linarith only [h0, h472, h506, h510, h512, h531, hc14, hlam, hphi, u4elo2]
                                                        · linarith only [h530, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h468, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h504, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p525_1, u4elo1]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h1, h468, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p525_1]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hc04, hlam, hphi, p525_1, u4elo2]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hc14, hlam, hphi, p525_1, u4elo2]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p525_1, u4elo2]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        rcases p525_3 (m.d 0 4) (by simp) with h544 | h544
                                                        · linarith only [h472, h544, hlam]
                                                        · linarith only [h501, h544, hlam]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h499, hlam, p525_1]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h507, hlam, p525_1]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h509, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p513_1, p525_1]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h501, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h507, hc34, hlam, hphi, p525_1, u4elo4]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h511, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [h512, hlam, p525_0]
                                                      · obtain ⟨p525_0, p525_1, p525_2, p525_3⟩ := h525c
                                                        linarith only [hlam, p525_0]
                                                    · rcases h4bigk with h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h504, hc12, hlam, hphi, ht23, ht34, p557_1, u4elo0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h472, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h1, h468, h512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p557_1]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        rcases p557_3 (m.d 0 4) (by simp) with h562 | h562
                                                        · rcases p557_3 (m.d 1 4) (by simp) with h563 | h563
                                                          · linarith only [h468, h563, hlam]
                                                          · linarith only [h504, h506, h510, h512, h563, hlam]
                                                        · linarith only [h562, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h468, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h504, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p557_1, u4elo1]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h1, h468, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p557_1]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hc04, hlam, hphi, p557_1, u4elo2]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hc14, hlam, hphi, p557_1, u4elo2]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p557_1, u4elo2]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        rcases p557_3 (m.d 0 4) (by simp) with h576 | h576
                                                        · linarith only [h472, h576, hlam]
                                                        · linarith only [h501, h576, hlam]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h499, hlam, p557_1]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h507, hlam, p557_1]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h509, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h1, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p513_1, p557_1]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h501, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h507, hc34, hlam, hphi, p557_1, u4elo4]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h511, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [h512, hlam, p557_0]
                                                      · obtain ⟨p557_0, p557_1, p557_2, p557_3⟩ := h557c
                                                        linarith only [hlam, p557_0]
                                                    · rcases h4bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h504, hc12, hlam, hphi, ht23, ht34, p589_1, u4elo0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h472, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h1, h468, h512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p589_1]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        rcases p589_3 (m.d 0 4) (by simp) with h594 | h594
                                                        · rcases p589_3 (m.d 1 4) (by simp) with h595 | h595
                                                          · linarith only [h468, h595, hlam]
                                                          · linarith only [h504, h506, h510, h512, h595, hlam]
                                                        · linarith only [h594, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h468, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h504, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p589_1, u4elo1]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h1, h468, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p589_1]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hc04, hlam, hphi, p589_1, u4elo2]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hc14, hlam, hphi, p589_1, u4elo2]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h512, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p589_1, u4elo2]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        rcases p589_3 (m.d 0 4) (by simp) with h608 | h608
                                                        · linarith only [h472, h608, hlam]
                                                        · linarith only [h501, h608, hlam]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h499, hlam, p589_1]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h507, hlam, p589_1]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h509, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h1, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p513_1, p589_1]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h501, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h507, hc34, hlam, hphi, p589_1, u4elo4]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h511, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [h512, hlam, p589_0]
                                                      · obtain ⟨p589_0, p589_1, p589_2, p589_3⟩ := h589c
                                                        linarith only [hlam, p589_0]
                                                    · linarith only [h507, h524, hlam, ht34, u4elo1]
                                                    · linarith only [h510, h524, hlam, ht34, ht45, u5elo2]
                                              · linarith only [h509, h519, hlam]
                                            · linarith only [h507, h518, hlam]
                                          · linarith only [h517, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          rcases p513_3 (m.d 0 3) (by simp) with h626 | h626
                                          · rcases p513_3 (m.d 1 3) (by simp) with h627 | h627
                                            · rcases p513_3 (m.d 2 3) (by simp) with h628 | h628
                                              · rcases p513_3 (m.d 3 4) (by simp) with h629 | h629
                                                · linarith only [h499, h629, hlam]
                                                · linarith only [h512, h629, hlam]
                                              · linarith only [h510, h628, hlam]
                                            · linarith only [h508, h627, hlam]
                                          · linarith only [h626, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, h468, h502, h504, hc12, hc23, hlam, hphi, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h502, hlam, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          rcases p513_3 (m.d 0 3) (by simp) with h638 | h638
                                          · linarith only [h1, h638, hlam]
                                          · linarith only [h499, h638, hlam]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, h468, h504, h506, h510, hlam, p513_2]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, h468, h504, h506, h510, h512, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, h468, h504, h506, h510, h512, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          rcases p513_3 (m.d 0 3) (by simp) with h645 | h645
                                          · linarith only [h470, h645, hlam]
                                          · linarith only [h499, h645, hlam]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, h468, h502, h504, h506, h510, hlam, p513_2]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h499, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h507, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h509, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h1, h468, h507, h512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p513_1]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h500, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h508, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h510, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [h512, hlam, p513_0]
                                        · obtain ⟨p513_0, p513_1, p513_2, p513_3⟩ := h513c
                                          linarith only [hlam, p513_0]
                                      · linarith only [h512, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h472, h501, h506, h510, h511, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h1, h468, h502, h504, h506, h510, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h468, h502, h504, h506, h509, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h468, h504, h506, h508, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h468, h504, h506, h507, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h506, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h501, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1, h500, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h499, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h498, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h469, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h468, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h672 | h672
    · rcases m.htr 0 1 4 (by decide) (by decide) with h673 | h673
      · rcases m.htr 0 1 5 (by decide) (by decide) with h674 | h674
        · rcases m.htr 0 2 3 (by decide) (by decide) with h675 | h675
          · rcases m.htr 0 2 4 (by decide) (by decide) with h676 | h676
            · rcases m.htr 0 2 5 (by decide) (by decide) with h677 | h677
              · rcases m.htr 0 3 4 (by decide) (by decide) with h678 | h678
                · rcases m.htr 0 3 5 (by decide) (by decide) with h679 | h679
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h680 | h680
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h681 | h681
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h682 | h682
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h683 | h683
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h684 | h684
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h685 | h685
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h687 | h687
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h688 | h688
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h689 | h689
                                      · linarith only [h0, h672, h681, h686, h689, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h689, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h680, h688, hc24, hlam, hphi, u4elo0]
                                  · linarith only [h687, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h0, h672, h684, h686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h685, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h696 | h696
                              · linarith only [h0, h672, h678, h684, h696, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h696, hc13, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h683, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h682, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h672, h675, h678, h681, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h680, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h678, h679, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h704 | h704
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h705 | h705
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h707 | h707
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h709 | h709
                            · linarith only [h672, h678, h704, h709, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h711 | h711
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                                · linarith only [h0, h672, h675, h678, h711, h712, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h715 | h715
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h716 | h716
                                      · rcases h3bigk with h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h678, h706, h714, h716, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h678, h714, h716, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h678, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h678, h716, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h672, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h0, h672, h714, h716, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p717_1]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h709, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h672, h678, h716, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h675, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h706, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h712, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h675, h678, h716, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hc03, hlam, hphi, ht34, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h706, hc23, hlam, hphi, ht34, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hc23, hlam, hphi, ht34, p717_1, u4elo3]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          rcases p717_3 (m.d 0 3) (by simp) with h737 | h737
                                          · linarith only [h678, h737, hlam]
                                          · linarith only [h704, h737, hlam]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h704, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h711, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h714, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [h716, hlam, p717_0]
                                        · obtain ⟨p717_0, p717_1, p717_2, p717_3⟩ := h717c
                                          linarith only [hlam, p717_0]
                                      · linarith only [h716, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h672, h678, h705, h706, h714, h715, hc24, hc35, hlam, hphi, u4elo3, u5elo0]
                                  · linarith only [h714, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h678, h704, h711, hc13, hlam, hphi, ht34, u4elo3]
                          · linarith only [h0, h708, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h672, h706, h707, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h675, h706, hlam]
                    · linarith only [h705, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h704, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h677, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h672, h676, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h672, h675, hlam]
        · linarith only [h672, h674, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · linarith only [h672, h673, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h759 | h759
      · rcases m.htr 0 1 5 (by decide) (by decide) with h760 | h760
        · rcases m.htr 0 2 3 (by decide) (by decide) with h761 | h761
          · rcases m.htr 0 2 4 (by decide) (by decide) with h762 | h762
            · rcases m.htr 0 2 5 (by decide) (by decide) with h763 | h763
              · rcases m.htr 0 3 4 (by decide) (by decide) with h764 | h764
                · rcases m.htr 0 3 5 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h766 | h766
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h767 | h767
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h768 | h768
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h769 | h769
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h770 | h770
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h772 | h772
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h774 | h774
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h775 | h775
                                      · rcases h3bigk with h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h672, hlam, p776_1]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h772, h775, hc03, hc45, hlam, hphi, ht0b, ht5b, p776_1]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          rcases p776_3 (m.d 0 3) (by simp) with h780 | h780
                                          · rcases p776_3 (m.d 1 3) (by simp) with h781 | h781
                                            · rcases p776_3 (m.d 2 3) (by simp) with h782 | h782
                                              · linarith only [h761, h782, hlam]
                                              · linarith only [h772, h782, hlam]
                                            · linarith only [h770, h781, hlam]
                                          · linarith only [h780, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          rcases p776_3 (m.d 0 3) (by simp) with h787 | h787
                                          · rcases p776_3 (m.d 1 3) (by simp) with h788 | h788
                                            · rcases p776_3 (m.d 2 3) (by simp) with h789 | h789
                                              · linarith only [h761, h789, hlam]
                                              · linarith only [h773, h789, hlam]
                                            · linarith only [h771, h788, hlam]
                                          · linarith only [h787, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h672, h759, h767, h768, h772, h775, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p776_1]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h767, h772, h775, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p776_1]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          rcases p776_3 (m.d 0 3) (by simp) with h797 | h797
                                          · linarith only [h672, h797, hlam]
                                          · linarith only [h764, h797, hlam]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          rcases p776_3 (m.d 0 3) (by simp) with h800 | h800
                                          · linarith only [h672, h800, hlam]
                                          · linarith only [h765, h800, hlam]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h761, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h767, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h761, h775, hc02, hc45, hlam, hphi, ht0b, ht5b, p776_1]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          rcases p776_3 (m.d 0 3) (by simp) with h807 | h807
                                          · rcases p776_3 (m.d 1 3) (by simp) with h808 | h808
                                            · rcases p776_3 (m.d 2 3) (by simp) with h809 | h809
                                              · rcases p776_3 (m.d 3 4) (by simp) with h810 | h810
                                                · linarith only [h772, h810, hlam]
                                                · linarith only [h775, h810, hlam]
                                              · linarith only [h809, hlam, p776_0]
                                            · linarith only [h771, h808, hlam]
                                          · linarith only [h765, h807, hlam]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h764, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h770, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h772, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h0, h759, h768, h772, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p776_1]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h765, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h771, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h773, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [h775, hlam, p776_0]
                                        · obtain ⟨p776_0, p776_1, p776_2, p776_3⟩ := h776c
                                          linarith only [hlam, p776_0]
                                      · linarith only [h775, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h766, h772, h774, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h772, h773, hc34, hlam, hphi, ht45, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h829 | h829
                                  · linarith only [h672, h759, h767, h770, h772, h829, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h829, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h672, h765, h771, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                            · linarith only [h672, h759, h768, h770, hc24, hlam, hphi, u4elo3]
                          · linarith only [h672, h759, h767, h768, h769, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h672, h767, h768, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                      · linarith only [h0, h761, h767, hlam]
                    · linarith only [h766, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h672, h759, h765, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h672, h759, h764, hc14, hlam, hphi, u4elo3]
              · linarith only [h763, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h672, h759, h761, h762, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h842 | h842
            · rcases m.htr 0 2 5 (by decide) (by decide) with h843 | h843
              · rcases m.htr 0 3 4 (by decide) (by decide) with h844 | h844
                · rcases m.htr 0 3 5 (by decide) (by decide) with h845 | h845
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h846 | h846
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h849 | h849
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h850 | h850
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h851 | h851
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h852 | h852
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h853 | h853
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h854 | h854
                                    · linarith only [h0, h759, h761, h847, h848, h854, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h846, h854, hc24, hlam, hphi, u4elo0]
                                  · linarith only [h0, h759, h761, h848, h852, h853, hc34, hlam, hphi, ht45, u5elo3]
                                · linarith only [h0, h761, h852, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                              · linarith only [h0, h761, h847, h851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h761, h847, h850, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h761, h847, h849, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h0, h761, h847, h848, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h866 | h866
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h867 | h867
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h868 | h868
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h869 | h869
                                    · linarith only [h0, h759, h847, h863, h869, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h867, h869, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h847, h868, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h759, h847, h863, h867, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h672, h866, hc03, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h759, h847, h863, h865, hc24, hlam, hphi, u4elo3]
                          · linarith only [h0, h759, h863, h864, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h759, h863, hc14, hlam, hphi, u4elo2]
                    · linarith only [h846, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h845, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h759, h761, h844, hc14, hlam, hphi, u4elo3]
              · linarith only [h0, h759, h843, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h759, h842, hc14, hlam, hphi, u4elo2]
        · linarith only [h759, h760, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h884 | h884
        · rcases m.htr 0 2 3 (by decide) (by decide) with h885 | h885
          · rcases m.htr 0 2 4 (by decide) (by decide) with h886 | h886
            · rcases m.htr 0 2 5 (by decide) (by decide) with h887 | h887
              · rcases m.htr 0 3 4 (by decide) (by decide) with h888 | h888
                · rcases m.htr 0 3 5 (by decide) (by decide) with h889 | h889
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h890 | h890
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h891 | h891
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h892 | h892
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h894 | h894
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h895 | h895
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h896 | h896
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h897 | h897
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h898 | h898
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h899 | h899
                                      · rcases h3bigk with h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c | h900c
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h672, hlam, p900_1]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h896, h899, hc03, hc45, hlam, hphi, ht0b, ht5b, p900_1]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          rcases p900_3 (m.d 0 3) (by simp) with h904 | h904
                                          · rcases p900_3 (m.d 1 3) (by simp) with h905 | h905
                                            · rcases p900_3 (m.d 2 3) (by simp) with h906 | h906
                                              · linarith only [h885, h906, hlam]
                                              · linarith only [h896, h906, hlam]
                                            · linarith only [h894, h905, hlam]
                                          · linarith only [h904, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          rcases p900_3 (m.d 0 3) (by simp) with h911 | h911
                                          · rcases p900_3 (m.d 1 3) (by simp) with h912 | h912
                                            · rcases p900_3 (m.d 2 3) (by simp) with h913 | h913
                                              · linarith only [h885, h913, hlam]
                                              · linarith only [h897, h913, hlam]
                                            · linarith only [h895, h912, hlam]
                                          · linarith only [h911, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h885, h891, h896, h899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p900_1]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h891, h896, h899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p900_1]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          rcases p900_3 (m.d 0 3) (by simp) with h921 | h921
                                          · linarith only [h672, h921, hlam]
                                          · linarith only [h888, h921, hlam]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          rcases p900_3 (m.d 0 3) (by simp) with h924 | h924
                                          · linarith only [h672, h924, hlam]
                                          · linarith only [h889, h924, hlam]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h885, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h891, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h885, h899, hc02, hc45, hlam, hphi, ht0b, ht5b, p900_1]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          rcases p900_3 (m.d 0 3) (by simp) with h931 | h931
                                          · rcases p900_3 (m.d 1 3) (by simp) with h932 | h932
                                            · rcases p900_3 (m.d 2 3) (by simp) with h933 | h933
                                              · rcases p900_3 (m.d 3 4) (by simp) with h934 | h934
                                                · linarith only [h896, h934, hlam]
                                                · linarith only [h899, h934, hlam]
                                              · linarith only [h933, hlam, p900_0]
                                            · linarith only [h895, h932, hlam]
                                          · linarith only [h889, h931, hlam]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h888, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h894, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h896, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h0, h885, h896, h899, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p900_1]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h889, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h895, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h897, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [h899, hlam, p900_0]
                                        · obtain ⟨p900_0, p900_1, p900_2, p900_3⟩ := h900c
                                          linarith only [hlam, p900_0]
                                      · linarith only [h899, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h890, h896, h898, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h759, h884, h893, h897, hc23, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h955 | h955
                                      · rcases h3bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h672, hlam, p956_1]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          rcases p956_3 (m.d 0 3) (by simp) with h959 | h959
                                          · rcases p956_3 (m.d 1 3) (by simp) with h960 | h960
                                            · rcases p956_3 (m.d 2 3) (by simp) with h961 | h961
                                              · linarith only [h885, h961, hlam]
                                              · rcases p956_3 (m.d 3 4) (by simp) with h963 | h963
                                                · linarith only [h888, h963, hlam]
                                                · linarith only [h896, h963, hlam]
                                            · linarith only [h891, h960, hlam]
                                          · linarith only [h885, h959, hlam]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h896, h953, h955, hc03, hc45, hlam, hphi, ht0b, ht5b, p956_1]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h888, h896, h953, hlam, p956_2]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h888, h896, h953, h955, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          rcases p956_3 (m.d 0 3) (by simp) with h972 | h972
                                          · linarith only [h672, h972, hlam]
                                          · linarith only [h885, h972, hlam]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h891, h896, h953, h955, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p956_1]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h672, h888, h896, h953, hlam, p956_2]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h885, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h891, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h896, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h888, h896, h955, hc03, hc45, hlam, hphi, ht0b, ht5b, p956_1]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h888, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h894, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [hc23, hlam, hphi, ht34, p956_1, u4elo3]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          rcases p956_3 (m.d 0 3) (by simp) with h986 | h986
                                          · rcases p956_3 (m.d 1 3) (by simp) with h987 | h987
                                            · rcases p956_3 (m.d 2 3) (by simp) with h988 | h988
                                              · linarith only [h896, h988, hlam]
                                              · linarith only [h953, h988, hlam]
                                            · linarith only [h895, h987, hlam]
                                          · linarith only [h889, h986, hlam]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h889, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h895, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h953, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [h955, hlam, p956_0]
                                        · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                          linarith only [hlam, p956_0]
                                      · linarith only [h896, h953, h955, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                    · linarith only [h890, h896, h953, h954, hc35, hlam, hphi, u5elo0]
                                  · linarith only [h953, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h759, h884, h889, h893, h894, h895, hc25, hlam, hphi, u5elo0]
                            · linarith only [h672, h884, h888, h893, h894, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h893, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h885, h888, h892, hc34, hlam, hphi, u4elo2]
                      · linarith only [h0, h885, h891, hlam]
                    · linarith only [h890, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h759, h888, h889, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1008 | h1008
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1009 | h1009
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1010 | h1010
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1011 | h1011
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1014 | h1014
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1015 | h1015
                                · linarith only [h1012, h1015, h672, h884, h885, h888, hc02, hc25, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
                                      · rcases h3bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h672, hlam, p1020_1]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1013, h1017, h1019, h888, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1020_1]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h888, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1019, h888, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1020_1, u4elo3]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          rcases p1020_3 (m.d 0 3) (by simp) with h1026 | h1026
                                          · linarith only [h1026, h672, hlam]
                                          · rcases p1020_3 (m.d 1 3) (by simp) with h1028 | h1028
                                            · rcases p1020_3 (m.d 2 3) (by simp) with h1029 | h1029
                                              · linarith only [h1010, h1029, hlam]
                                              · rcases p1020_3 (m.d 3 4) (by simp) with h1031 | h1031
                                                · linarith only [h1013, h1031, hlam]
                                                · linarith only [h1031, h888, hlam]
                                            · linarith only [h1028, h672, hlam]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          rcases p1020_3 (m.d 0 3) (by simp) with h1036 | h1036
                                          · linarith only [h1036, h672, hlam]
                                          · linarith only [h1036, h885, hlam]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1010, h1012, h1017, h1019, h672, h884, h888, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1020_1]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1012, h1013, h1017, h672, h884, h888, hlam, p1020_2]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h885, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1010, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1015, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1019, h885, h888, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1020_1, u4elo3]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [hc03, hlam, hphi, ht34, p1020_1, u4elo3]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1013, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1013, hc23, hlam, hphi, ht34, p1020_1, u4elo1]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          rcases p1020_3 (m.d 0 3) (by simp) with h1050 | h1050
                                          · linarith only [h1050, h888, hlam]
                                          · linarith only [h1008, h1050, hlam]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1008, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1014, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1017, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [h1019, hlam, p1020_0]
                                        · obtain ⟨p1020_0, p1020_1, p1020_2, p1020_3⟩ := h1020c
                                          linarith only [hlam, p1020_0]
                                      · linarith only [h1019, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1009, h1015, h1017, h1018, hc35, hlam, hphi, u5elo0]
                                  · linarith only [h1017, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h1008, h1013, h1014, h888, hlam]
                            · linarith only [h1012, h1013, h672, h884, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h1012, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1010, h1011, h672, h884, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                      · linarith only [h0, h1010, h885, hlam]
                    · linarith only [h1009, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1008, h672, h884, hc15, hlam, hphi, u5elo3]
              · linarith only [h887, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h885, h886, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1070 | h1070
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1071 | h1071
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1072 | h1072
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1073 | h1073
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1074 | h1074
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1075 | h1075
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1076 | h1076
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1077 | h1077
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1078 | h1078
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1079 | h1079
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1080 | h1080
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1081 | h1081
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1082 | h1082
                                    · linarith only [h1070, h1075, h1082, h885, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h1082, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h1077, h1081, h759, h884, h885, hc02, hc25, hlam, hphi, ht23, ht34, u4elo1, u5elo3]
                                · linarith only [h1070, h1080, h885, hc24, hlam, hphi, u4elo3]
                              · linarith only [h1070, h1075, h1077, h1079, h759, h884, h885, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1070, h1072, h1075, h1077, h1078, h759, h884, h885, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1075, h1077, h885, hc03, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h1070, h1075, h1076, h885, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1093 | h1093
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1094 | h1094
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1096 | h1096
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1098 | h1098
                                      · rcases h3bigk with h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h672, hlam, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h885, hlam, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          rcases p1099_3 (m.d 0 3) (by simp) with h1103 | h1103
                                          · rcases p1099_3 (m.d 1 3) (by simp) with h1104 | h1104
                                            · rcases p1099_3 (m.d 2 3) (by simp) with h1105 | h1105
                                              · rcases p1099_3 (m.d 3 4) (by simp) with h1106 | h1106
                                                · linarith only [h1106, hlam, p1099_0]
                                                · rcases p1099_3 (m.d 3 5) (by simp) with h1108 | h1108
                                                  · linarith only [h1073, h1108, hlam]
                                                  · rcases h3emin with h1110 | h1110 | h1110 | h1110 | h1110
                                                    · rcases h4bigk with h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h759, hlam, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1095, h1098, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1111_1, u4elo0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1098, h759, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1111_1, u4elo1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        rcases p1111_3 (m.d 0 4) (by simp) with h1116 | h1116
                                                        · rcases p1111_3 (m.d 1 4) (by simp) with h1117 | h1117
                                                          · rcases p1111_3 (m.d 2 4) (by simp) with h1118 | h1118
                                                            · linarith only [h1070, h1118, hlam]
                                                            · linarith only [h1097, h1118, hlam]
                                                          · linarith only [h1092, h1096, h1098, h1117, h759, h884, hlam]
                                                        · linarith only [h1116, hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hc04, hlam, hphi, p1111_1, u4elo1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1095, h1098, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1111_1, u4elo1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1098, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1111_1, u4elo1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        rcases p1111_3 (m.d 0 4) (by simp) with h1127 | h1127
                                                        · linarith only [h1127, h759, hlam]
                                                        · linarith only [h1074, h1127, hlam]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1070, hlam, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1091, hlam, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1070, h1098, hc02, hc45, hlam, hphi, ht0b, ht5b, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h0, h1070, h1075, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1072, hlam, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1093, hlam, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1095, hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p1099_1, p1111_1]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1074, hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hc14, hlam, hphi, p1111_1, u4elo4]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1097, hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [h1098, hlam, p1111_0]
                                                      · obtain ⟨p1111_0, p1111_1, p1111_2, p1111_3⟩ := h1111c
                                                        linarith only [hlam, p1111_0]
                                                    · rcases h4bigk with h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h759, hlam, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hc24, hlam, hphi, p1145_1, u4elo0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h759, hc34, hlam, hphi, p1145_1, u4elo1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        rcases p1145_3 (m.d 0 4) (by simp) with h1150 | h1150
                                                        · rcases p1145_3 (m.d 1 4) (by simp) with h1151 | h1151
                                                          · rcases p1145_3 (m.d 2 4) (by simp) with h1152 | h1152
                                                            · linarith only [h1070, h1152, hlam]
                                                            · linarith only [h1097, h1152, hlam]
                                                          · linarith only [h1095, h1098, h1151, h759, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                                                        · linarith only [h1150, hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hc04, hlam, hphi, p1145_1, u4elo1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hc24, hlam, hphi, p1145_1, u4elo1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hc34, hlam, hphi, p1145_1, u4elo1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        rcases p1145_3 (m.d 0 4) (by simp) with h1161 | h1161
                                                        · linarith only [h1161, h759, hlam]
                                                        · linarith only [h1074, h1161, hlam]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1070, hlam, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1091, hlam, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1098, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1145_1, u4elo2]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h0, h1070, h1075, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1072, hlam, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1093, hlam, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1095, hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1099_1, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1074, hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1092, h1096, h1098, h759, h884, hlam, p1145_1]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1097, hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [h1098, hlam, p1145_0]
                                                      · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                        linarith only [hlam, p1145_0]
                                                    · rcases h4bigk with h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c | h1179c
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h759, hlam, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hc24, hlam, hphi, p1179_1, u4elo0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h759, hc34, hlam, hphi, p1179_1, u4elo1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        rcases p1179_3 (m.d 0 4) (by simp) with h1184 | h1184
                                                        · rcases p1179_3 (m.d 1 4) (by simp) with h1185 | h1185
                                                          · rcases p1179_3 (m.d 2 4) (by simp) with h1186 | h1186
                                                            · linarith only [h1070, h1186, hlam]
                                                            · linarith only [h1097, h1186, hlam]
                                                          · linarith only [h1092, h1096, h1098, h1185, h759, h884, hlam]
                                                        · linarith only [h1184, hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hc04, hlam, hphi, p1179_1, u4elo1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hc24, hlam, hphi, p1179_1, u4elo1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hc34, hlam, hphi, p1179_1, u4elo1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        rcases p1179_3 (m.d 0 4) (by simp) with h1195 | h1195
                                                        · linarith only [h1195, h759, hlam]
                                                        · linarith only [h1074, h1195, hlam]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1070, hlam, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1091, hlam, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1098, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1179_1, u4elo2]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h0, h1070, h1075, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1072, hlam, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1093, hlam, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1095, hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1075, h672, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1099_1, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1074, hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1092, h1096, h1098, h759, h884, hlam, p1179_1]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1097, hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [h1098, hlam, p1179_0]
                                                      · obtain ⟨p1179_0, p1179_1, p1179_2, p1179_3⟩ := h1179c
                                                        linarith only [hlam, p1179_0]
                                                    · linarith only [h1075, h1110, h672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1099_1]
                                                    · linarith only [h1092, h1096, h1110, h759, h884, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                              · linarith only [h1095, h1105, hlam]
                                            · linarith only [h1093, h1104, hlam]
                                          · linarith only [h1103, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          rcases p1099_3 (m.d 0 3) (by simp) with h1218 | h1218
                                          · rcases p1099_3 (m.d 1 3) (by simp) with h1219 | h1219
                                            · rcases p1099_3 (m.d 2 3) (by simp) with h1220 | h1220
                                              · rcases p1099_3 (m.d 3 4) (by simp) with h1221 | h1221
                                                · linarith only [h1072, h1221, hlam]
                                                · linarith only [h1098, h1221, hlam]
                                              · linarith only [h1096, h1220, hlam]
                                            · linarith only [h1094, h1219, hlam]
                                          · linarith only [h1218, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1070, h1075, h1097, h885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1075, hlam, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          rcases p1099_3 (m.d 0 3) (by simp) with h1230 | h1230
                                          · linarith only [h1230, h672, hlam]
                                          · linarith only [h1072, h1230, hlam]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          rcases p1099_3 (m.d 0 3) (by simp) with h1233 | h1233
                                          · linarith only [h1233, h672, hlam]
                                          · linarith only [h1073, h1233, hlam]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1070, h1095, h1098, h885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h672, hc01, hc23, hlam, hphi, ht12, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          rcases p1099_3 (m.d 0 3) (by simp) with h1239 | h1239
                                          · linarith only [h1239, h885, hlam]
                                          · linarith only [h1072, h1239, hlam]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1075, h1091, h1092, h1096, h759, h884, hlam, p1099_2]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1072, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1093, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1095, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h0, h1070, h1075, h1095, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1099_1]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1073, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1094, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1096, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [h1098, hlam, p1099_0]
                                        · obtain ⟨p1099_0, p1099_1, p1099_2, p1099_3⟩ := h1099c
                                          linarith only [hlam, p1099_0]
                                      · linarith only [h1098, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1074, h1097, hc24, hlam, hphi, u4elo0]
                                  · linarith only [h0, h1075, h1092, h1096, h759, h884, hc02, hc25, hlam, hphi, ht23, ht34, u4elo1, u5elo3]
                                · linarith only [h1075, h1091, h1092, h1095, h759, h884, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1075, h1091, h1092, h1094, h759, h884, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1072, h1075, h1091, h1092, h1093, h759, h884, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1091, h1092, h759, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1091, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h1074, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1073, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1070, h1072, h885, hc24, hlam, hphi, u4elo3]
              · linarith only [h1070, h1071, h759, h884, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1265 | h1265
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1266 | h1266
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1267 | h1267
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1268 | h1268
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1269 | h1269
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1270 | h1270
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1271 | h1271
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1272 | h1272
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1273 | h1273
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1274 | h1274
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1275 | h1275
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1276 | h1276
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1277 | h1277
                                      · rcases h3bigk with h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h672, hlam, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h885, hlam, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1269, h1277, h885, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          rcases p1278_3 (m.d 0 3) (by simp) with h1283 | h1283
                                          · rcases p1278_3 (m.d 1 3) (by simp) with h1284 | h1284
                                            · rcases p1278_3 (m.d 2 3) (by simp) with h1285 | h1285
                                              · rcases p1278_3 (m.d 3 4) (by simp) with h1286 | h1286
                                                · linarith only [h1266, h1286, hlam]
                                                · linarith only [h1277, h1286, hlam]
                                              · linarith only [h1275, h1285, hlam]
                                            · linarith only [h1273, h1284, hlam]
                                          · linarith only [h1283, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1266, h1277, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h0, h1269, h1271, h1275, h1277, h884, h885, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          rcases p1278_3 (m.d 0 3) (by simp) with h1295 | h1295
                                          · linarith only [h1295, h672, hlam]
                                          · linarith only [h1266, h1295, hlam]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          rcases p1278_3 (m.d 0 3) (by simp) with h1298 | h1298
                                          · linarith only [h1298, h672, hlam]
                                          · linarith only [h1267, h1298, hlam]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1266, h1277, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1269, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1269, h1277, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          rcases p1278_3 (m.d 0 3) (by simp) with h1305 | h1305
                                          · linarith only [h1305, h885, hlam]
                                          · linarith only [h1267, h1305, hlam]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1266, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1272, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1274, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1266, h1269, h1277, h885, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1278_1]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1267, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1273, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1275, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [h1277, hlam, p1278_0]
                                        · obtain ⟨p1278_0, p1278_1, p1278_2, p1278_3⟩ := h1278c
                                          linarith only [hlam, p1278_0]
                                      · linarith only [h1277, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h1070, h1268, h1276, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h0, h1070, h1270, h1271, h1275, h884, h885, hc03, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                                · linarith only [h0, h1271, h1274, h884, h885, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                              · linarith only [h0, h1070, h1270, h1271, h1272, h1273, h884, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1266, h1271, h1272, h672, h884, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h1070, h1269, h1270, h1271, h884, h885, hc03, hc15, hlam, hphi, ht34, u4elo1, u5elo2]
                        · linarith only [h0, h1269, h1270, h884, h885, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1326 | h1326
                        · linarith only [h0, h1070, h1269, h1326, h884, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1326, h884, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h0, h1070, h1268, h884, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1266, h1267, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1331 | h1331
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1332 | h1332
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1333 | h1333
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1334 | h1334
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1335 | h1335
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1337 | h1337
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1338 | h1338
                                · linarith only [h0, h1266, h1333, h1335, h1338, h884, h885, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h1335, h1336, h1338, h884, h885, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                              · linarith only [h1337, hc13, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h1333, h1335, h1336, h884, h885, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h1070, h1335, h884, hc12, hc15, hlam, hphi, ht23, ht34, u4elo2, u5elo2]
                        · linarith only [h1333, h1334, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1345 | h1345
                        · linarith only [h0, h1070, h1333, h1345, h884, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1345, h884, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                    · linarith only [h1332, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1331, h884, h885, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h1265, h884, hc15, hlam, hphi, u5elo2]
        · linarith only [h884, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
