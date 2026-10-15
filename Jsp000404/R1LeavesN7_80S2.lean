import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_13_25_L_0_L_I_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h2, h5, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                · linarith only [h11, h4, h5, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h4, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h15, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                    · linarith only [h15, h5, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · linarith only [h0, h18, h19, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h22, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · linarith only [h1, h18, h24, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2, h24, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · linarith only [h2, h3, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
            · linarith only [h2, h28, h30, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
              · linarith only [h0, h32, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · linarith only [h2, h28, h32, hc13, hc34, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
            · linarith only [h2, h28, h35, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
              · linarith only [h1, h29, h37, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
              · linarith only [h2, h28, h37, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
            · linarith only [h0, h28, h41, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
              · linarith only [h0, h28, h43, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                · linarith only [h0, h2, h40, h45, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                  · linarith only [h0, h28, h40, h47, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                    · rcases h3bigk with h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h28, hc13, hlam, hphi, ht34, ht45, p50_1, u5elo3]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h28, hc23, hlam, hphi, ht34, ht45, p50_1, u5elo3]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h2, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h28, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h0, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1, u0elo0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h41, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h43, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h1, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h40, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h45, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h47, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        rcases p50_3 (m.d 0 3) (by simp) with h66 | h66
                        · linarith only [h66, hlam, p50_0]
                        · rcases p50_3 (m.d 1 3) (by simp) with h68 | h68
                          · linarith only [h41, h68, hlam]
                          · rcases p50_3 (m.d 2 3) (by simp) with h70 | h70
                            · linarith only [h45, h70, hlam]
                            · rcases p50_3 (m.d 3 4) (by simp) with h72 | h72
                              · rcases p50_3 (m.d 3 5) (by simp) with h73 | h73
                                · linarith only [h49, h73, hlam]
                                · linarith only [h28, h73, hlam]
                              · linarith only [h72, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        rcases p50_3 (m.d 0 3) (by simp) with h77 | h77
                        · linarith only [h2, h77, hlam]
                        · linarith only [h0, h77, hlam]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        rcases p50_3 (m.d 0 3) (by simp) with h80 | h80
                        · linarith only [h2, h80, hlam]
                        · linarith only [h1, h80, hlam]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h28, hc03, hc34, hlam, hphi, p50_1]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h0, hc13, hlam, hphi, ht34, ht45, p50_1, u5elo3]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h40, hc23, hlam, hphi, ht34, ht45, p50_1, u5elo3]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [hc23, hlam, hphi, ht34, ht45, p50_1, u5elo3]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [h49, hlam, p50_0]
                      · have p50_0 := h50c.1
                        have p50_1 := h50c.2.1
                        have p50_2 := h50c.2.2.1
                        have p50_3 := h50c.2.2.2
                        linarith only [hlam, p50_0]
                    · linarith only [h0, h2, h40, h49, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1, h28, h40, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h92 | h92
      · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
        · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
          · linarith only [h0, h1, h93, h94, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
            · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
              · linarith only [h0, h97, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · linarith only [h93, h96, h97, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
              · linarith only [h0, h100, h92, h96, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                    · linarith only [h0, h104, h92, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi9]
                    · linarith only [h104, h94, h96, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h103, h92, h94, h96, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h102, h92, hlam]
        · linarith only [h92, h93, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
        · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
          · linarith only [h0, h1, h110, h111, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
            · linarith only [h0, h110, h113, h92, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
              · linarith only [h0, h115, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
              · linarith only [h110, h115, h92, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
          · linarith only [h0, h1, h110, h118, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
            · linarith only [h0, h120, h92, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
              · linarith only [h0, h110, h122, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                    · rcases h3bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h110, h118, h125, hc12, hlam, hphi, ht23, ht34, ht45, p127_1, u5elo2]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h1, hlam, p127_1]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h92, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h110, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h0, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h118, hlam, p127_1]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h120, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h122, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        rcases p127_3 (m.d 0 3) (by simp) with h138 | h138
                        · linarith only [h1, h138, hlam]
                        · rcases p127_3 (m.d 1 3) (by simp) with h140 | h140
                          · linarith only [h118, h140, hlam]
                          · rcases p127_3 (m.d 2 3) (by simp) with h142 | h142
                            · rcases p127_3 (m.d 3 4) (by simp) with h143 | h143
                              · linarith only [h124, h143, hlam]
                              · linarith only [h143, h92, hlam]
                            · linarith only [h1, h142, hlam]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        rcases p127_3 (m.d 0 3) (by simp) with h147 | h147
                        · linarith only [h1, h147, hlam]
                        · linarith only [h0, h147, hlam]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h126, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p127_1, u5ehi9]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h0, h110, h118, hc12, hc23, hlam, hphi, p127_1]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h0, h118, h124, hc12, hc23, hlam, hphi, p127_1]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h118, h124, hc12, hc23, hlam, hphi, p127_1]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h124, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h0, h110, h118, h124, hc12, hc23, hlam, hphi, p127_1]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h0, h118, h125, hc12, hlam, hphi, ht23, ht34, ht45, p127_1, u5elo2]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h118, h125, hc12, hlam, hphi, ht23, ht34, ht45, p127_1, u5elo2]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h125, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [h126, hlam, p127_0]
                      · have p127_0 := h127c.1
                        have p127_1 := h127c.2.1
                        have p127_2 := h127c.2.2.1
                        have p127_3 := h127c.2.2.2
                        linarith only [hlam, p127_0]
                    · linarith only [h0, h118, h126, h92, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h125, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                  · linarith only [h0, h110, h118, h124, h165, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h165, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h168 | h168
    · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
      · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
        · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
          · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
            · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
              · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                  · linarith only [h168, h175, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · linarith only [h170, h174, h175, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                  · linarith only [h168, h169, h174, h178, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                    · linarith only [h168, h169, h180, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
                    · linarith only [h174, h180, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h170, h173, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h0, h169, h170, h172, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi8]
          · linarith only [h0, h168, h170, h171, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
        · linarith only [h169, h170, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
        · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
          · rcases m.htr 1 3 4 (by decide) (by decide) with h189 | h189
            · linarith only [h169, h187, h189, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
              · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
                · linarith only [h168, h189, h192, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                  · linarith only [h168, h194, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
                  · linarith only [h0, h187, h189, h194, hc23, hc34, hlam, hphi]
              · linarith only [h0, h187, h191, hlam]
          · linarith only [h0, h168, h187, h188, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi8]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
          · rcases m.htr 1 3 4 (by decide) (by decide) with h200 | h200
            · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                · linarith only [h168, h169, h202, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                  · linarith only [h168, h187, h204, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                    · rcases h3bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h0, hlam, p207_1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h187, h201, hc23, hlam, hphi, ht34, ht45, p207_1, u5elo1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h169, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h187, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        rcases p207_3 (m.d 0 3) (by simp) with h213 | h213
                        · linarith only [h0, h213, hlam]
                        · rcases p207_3 (m.d 1 3) (by simp) with h215 | h215
                          · rcases p207_3 (m.d 2 3) (by simp) with h216 | h216
                            · linarith only [h199, h216, hlam]
                            · rcases p207_3 (m.d 3 4) (by simp) with h218 | h218
                              · linarith only [h200, h218, hlam]
                              · linarith only [h169, h218, hlam]
                          · linarith only [h0, h215, hlam]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        rcases p207_3 (m.d 0 3) (by simp) with h223 | h223
                        · linarith only [h0, h223, hlam]
                        · linarith only [h168, h223, hlam]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h199, h206, hc12, hlam, hphi, ht01, ht0b, ht5b, p207_1, u5ehi9]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h0, h187, h199, hc01, hc12, hlam, hphi, p207_1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h168, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h199, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h202, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h204, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h0, h199, h200, hc01, hc12, hlam, hphi, p207_1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h200, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        rcases p207_3 (m.d 0 3) (by simp) with h235 | h235
                        · linarith only [h169, h235, hlam]
                        · linarith only [h168, h235, hlam]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h0, h187, h199, h200, hc01, hc12, hlam, hphi, p207_1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h0, h201, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p207_1, u5elo1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h201, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h201, hc23, hlam, hphi, ht34, ht45, p207_1, u5elo1]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [h206, hlam, p207_0]
                      · have p207_0 := h207c.1
                        have p207_1 := h207c.2.1
                        have p207_2 := h207c.2.2.1
                        have p207_3 := h207c.2.2.2
                        linarith only [hlam, p207_0]
                    · linarith only [h0, h169, h206, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h201, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h247 | h247
              · linarith only [h0, h187, h200, h247, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h247, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h168, h187, h199, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h251 | h251
      · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
        · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
          · rcases m.htr 1 3 4 (by decide) (by decide) with h254 | h254
            · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
              · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                    · linarith only [h251, h258, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
                    · rcases h3bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h0, hlam, p260_1]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h168, hlam, p260_1]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        rcases p260_3 (m.d 0 3) (by simp) with h264 | h264
                        · rcases p260_3 (m.d 1 3) (by simp) with h265 | h265
                          · rcases p260_3 (m.d 2 3) (by simp) with h266 | h266
                            · rcases p260_3 (m.d 3 4) (by simp) with h267 | h267
                              · linarith only [h267, hlam, p260_0]
                              · rcases p260_3 (m.d 3 5) (by simp) with h269 | h269
                                · linarith only [h252, h269, hlam]
                                · linarith only [h258, h269, hlam]
                            · linarith only [h256, h266, hlam]
                          · linarith only [h254, h265, hlam]
                        · linarith only [h264, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [hlam, hphi, ht0b, ht5b, p260_1, u0elo2, u5ehi8]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h252, hc13, hlam, hphi, ht01, ht0b, ht5b, p260_1, u5ehi8]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h168, h252, h253, hc12, hlam, hphi, ht01, ht0b, ht5b, p260_1, u5ehi8]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        rcases p260_3 (m.d 0 3) (by simp) with h279 | h279
                        · linarith only [h0, h279, hlam]
                        · linarith only [h251, h279, hlam]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        rcases p260_3 (m.d 0 3) (by simp) with h282 | h282
                        · linarith only [h0, h282, hlam]
                        · linarith only [h252, h282, hlam]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h252, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p260_1, u5ehi8]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h253, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        rcases p260_3 (m.d 0 3) (by simp) with h288 | h288
                        · linarith only [h168, h288, hlam]
                        · linarith only [h251, h288, hlam]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h253, hc12, hlam, hphi, ht01, ht0b, ht5b, p260_1, u5ehi8]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h251, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h254, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h256, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h258, hlam, p260_1]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h252, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h255, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h257, hlam, p260_0]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [h252, hc34, hlam, hphi, ht0b, ht45, ht5b, p260_1, u0elo2]
                      · have p260_0 := h260c.1
                        have p260_1 := h260c.2.1
                        have p260_2 := h260c.2.2.1
                        have p260_3 := h260c.2.2.2
                        linarith only [hlam, p260_0]
                  · linarith only [h168, h252, h257, hlam]
                · linarith only [h168, h251, h256, hlam]
              · linarith only [h0, h252, h255, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h168, h251, h253, h254, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
            · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
              · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                    · linarith only [h251, h310, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
                    · rcases h3bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h0, hlam, p312_1]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h168, hlam, p312_1]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        rcases p312_3 (m.d 0 3) (by simp) with h316 | h316
                        · rcases p312_3 (m.d 1 3) (by simp) with h317 | h317
                          · rcases p312_3 (m.d 2 3) (by simp) with h318 | h318
                            · rcases p312_3 (m.d 3 4) (by simp) with h319 | h319
                              · linarith only [h319, hlam, p312_0]
                              · rcases p312_3 (m.d 3 5) (by simp) with h321 | h321
                                · linarith only [h252, h321, hlam]
                                · linarith only [h310, h321, hlam]
                            · linarith only [h308, h318, hlam]
                          · linarith only [h306, h317, hlam]
                        · linarith only [h316, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [hlam, hphi, ht0b, ht5b, p312_1, u0elo2, u5ehi8]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h252, h253, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u5ehi8]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h253, hlam, p312_1]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        rcases p312_3 (m.d 0 3) (by simp) with h331 | h331
                        · linarith only [h0, h331, hlam]
                        · linarith only [h251, h331, hlam]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        rcases p312_3 (m.d 0 3) (by simp) with h334 | h334
                        · linarith only [h0, h334, hlam]
                        · linarith only [h252, h334, hlam]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h252, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p312_1, u5ehi8]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p312_1]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        rcases p312_3 (m.d 0 3) (by simp) with h340 | h340
                        · linarith only [h168, h340, hlam]
                        · linarith only [h251, h340, hlam]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        rcases p312_3 (m.d 0 3) (by simp) with h343 | h343
                        · linarith only [h168, h343, hlam]
                        · linarith only [h252, h343, hlam]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h251, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h306, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h308, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h310, hlam, p312_1]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h252, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h307, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h309, hlam, p312_0]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [h252, hc34, hlam, hphi, ht0b, ht45, ht5b, p312_1, u0elo2]
                      · have p312_0 := h312c.1
                        have p312_1 := h312c.2.1
                        have p312_2 := h312c.2.2.1
                        have p312_3 := h312c.2.2.2
                        linarith only [hlam, p312_0]
                  · linarith only [h168, h252, h309, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h251, h253, h308, hlam]
              · linarith only [h0, h252, h307, hlam]
            · linarith only [h0, h251, h306, hlam]
        · linarith only [h251, h252, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h361 | h361
        · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
          · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
            · linarith only [h251, h361, h363, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
              · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                · linarith only [h0, h363, h366, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h368 | h368
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h369 | h369
                    · rcases h3bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h0, hlam, p370_1]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h168, hlam, p370_1]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h251, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h369, hlam, hphi, ht0b, ht5b, p370_1, u0elo2, u5ehi9]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h363, hc03, hc34, hlam, hphi, p370_1]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h363, hc23, hc34, hlam, hphi, p370_1]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h363, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h363, h369, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p370_1, u5ehi9]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h361, h369, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p370_1, u5ehi9]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h362, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h366, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h362, h363, h369, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p370_1, u5ehi9]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h361, h369, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p370_1, u5ehi9]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p370_1]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h168, h361, h369, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p370_1, u5ehi9]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        rcases p370_3 (m.d 0 3) (by simp) with h390 | h390
                        · linarith only [h251, h390, hlam]
                        · linarith only [h361, h390, hlam]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h361, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h365, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h368, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [h369, hlam, p370_0]
                      · have p370_0 := h370c.1
                        have p370_1 := h370c.2.1
                        have p370_2 := h370c.2.2.1
                        have p370_3 := h370c.2.2.2
                        linarith only [hlam, p370_0]
                    · linarith only [h251, h369, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h168, h361, h368, hlam]
              · linarith only [h168, h361, h362, h365, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
            · linarith only [h251, h361, h401, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
              · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                · linarith only [h0, h401, h404, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                    · rcases h3bigk with h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h0, hlam, p408_1]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h168, hlam, p408_1]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h251, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h407, hlam, hphi, ht0b, ht5b, p408_1, u0elo2, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h361, h401, h407, hc14, hlam, hphi, ht01, ht0b, ht5b, p408_1, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h362, hlam, p408_1]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h401, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h362, h404, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p408_1, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h361, h404, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p408_1, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h404, hc13, hc34, hlam, hphi, p408_1]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h404, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h404, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p408_1, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h361, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p408_1, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h0, h361, h407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p408_1, u5ehi9]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h362, hc12, hc34, hlam, hphi, ht23, p408_1]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        rcases p408_3 (m.d 0 3) (by simp) with h428 | h428
                        · linarith only [h251, h428, hlam]
                        · linarith only [h361, h428, hlam]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h361, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h403, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h406, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [h407, hlam, p408_0]
                      · have p408_0 := h408c.1
                        have p408_1 := h408c.2.1
                        have p408_2 := h408c.2.2.1
                        have p408_3 := h408c.2.2.2
                        linarith only [hlam, p408_0]
                    · linarith only [h251, h407, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h361, h362, h406, hlam]
              · linarith only [h0, h361, h403, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
          · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
            · rcases m.htr 1 3 5 (by decide) (by decide) with h441 | h441
              · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
                · linarith only [h0, h251, h439, h442, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h444 | h444
                  · linarith only [h439, h440, h442, h444, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · linarith only [h168, h441, h444, hc02, hlam, hphi, ht23, ht34, ht45, u5elo1]
              · linarith only [h251, h440, h441, hc04, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
              · linarith only [h0, h361, h440, h448, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h448, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
            · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
              · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                    · rcases h3bigk with h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, hlam, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h168, hlam, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h251, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h361, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        rcases p456_3 (m.d 0 3) (by simp) with h462 | h462
                        · linarith only [h0, h462, hlam]
                        · rcases p456_3 (m.d 1 3) (by simp) with h464 | h464
                          · rcases p456_3 (m.d 2 3) (by simp) with h465 | h465
                            · rcases p456_3 (m.d 3 4) (by simp) with h466 | h466
                              · linarith only [h451, h466, hlam]
                              · linarith only [h251, h466, hlam]
                            · linarith only [h168, h465, hlam]
                          · linarith only [h0, h464, hlam]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h439, hlam, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h361, h452, h455, hc01, hc13, hlam, hphi, p456_1, u5ehi9, u5elo1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h361, h439, hc01, hc23, hlam, hphi, ht12, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        rcases p456_3 (m.d 0 3) (by simp) with h475 | h475
                        · linarith only [h168, h475, hlam]
                        · rcases p456_3 (m.d 1 3) (by simp) with h477 | h477
                          · linarith only [h439, h477, hlam]
                          · linarith only [h0, h477, hlam]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h361, h452, h455, hc01, hc23, hlam, hphi, ht12, p456_1, u5ehi9, u5elo1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h361, hc01, hc23, hlam, hphi, ht12, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h451, hc01, hc13, hlam, hphi, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h451, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h453, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h361, h439, h451, hc01, hc23, hlam, hphi, ht12, p456_1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h0, h452, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p456_1, u5elo1]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h452, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h454, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [h455, hlam, p456_0]
                      · have p456_0 := h456c.1
                        have p456_1 := h456c.2.1
                        have p456_2 := h456c.2.2.1
                        have p456_3 := h456c.2.2.2
                        linarith only [hlam, p456_0]
                    · linarith only [h0, h251, h455, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h439, h452, h454, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                · linarith only [h439, h451, h453, hlam]
              · linarith only [h0, h251, h451, h452, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h498 | h498
              · linarith only [h0, h361, h451, h498, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h498, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h10, h12, h13, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h10, h15, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h12, h15, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h10, h18, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                            · linarith only [h12, h20, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h10, h20, h22, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h10, h12, h18, h24, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                                  · linarith only [h10, h20, h24, h26, h9, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h12, h26, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h29, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                        · linarith only [h31, h8, h9, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h2, h33, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                            · linarith only [h0, h31, h33, h35, h5, h7, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                              · linarith only [h0, h33, h37, h5, h7, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                                · linarith only [h0, h33, h39, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · linarith only [h0, h39, h5, h7, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                      · linarith only [h43, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h4, h42, h46, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                              · linarith only [h0, h4, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h49, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h42, h48, h8, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h42, h45, h8, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h4, h54, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h1, h56, h57, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                              · linarith only [h0, h4, h60, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h60, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h56, h59, h8, hc13, hlam, hphi, u1ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                          · linarith only [h2, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                            · linarith only [h0, h4, h56, h66, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h66, h8, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h71, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                          · linarith only [h0, h6, h69, h7, h71, h73, h74, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                            · linarith only [h0, h6, h69, h71, h76, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h6, h69, h71, h73, h76, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                          · linarith only [h6, h7, h71, h79, hc14, hlam, hphi, u1ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h6, h69, h71, h81, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h0, h6, h70, h71, h81, h83, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h6, h7, h70, h71, h85, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                                  · linarith only [h6, h7, h70, h71, h81, h87, hc23, hc34, hlam, hphi]
                                  · linarith only [h73, h87, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h5, h7, h70, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h4, h69, h92, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                          · linarith only [h0, h4, h69, h7, h91, h95, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                              · linarith only [h0, h4, h98, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h69, h91, h98, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                            · linarith only [h69, h91, h97, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h69, h91, h94, hlam]
                    · linarith only [h5, h7, h91, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h104 | h104
                · linarith only [h104, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                      · linarith only [h0, h108, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h104, h111, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                              · linarith only [h0, h106, h114, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                                · linarith only [h0, h104, h106, h113, h114, h116, h2, h6, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                                · linarith only [h0, h106, h113, h116, h6, hc34, hc45, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                              · linarith only [h119, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h0, h106, h110, h113, h119, h6, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                          · linarith only [h122, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                            · linarith only [h110, h124, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                              · linarith only [h126, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                                · linarith only [h0, h104, h107, h110, h126, h128, h2, h6, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                                  · linarith only [h0, h107, h124, h128, h130, h6, hc23, hc34, hlam, hphi]
                                  · linarith only [h110, h130, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h107, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h106, h4, h6, hc25, hlam, hphi, ht12, u1ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h135 | h135
              · linarith only [h135, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · linarith only [h0, h139, h5, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                      · linarith only [h1, h135, h141, h4, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                        · linarith only [h138, h139, h143, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                          · linarith only [h145, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h137, h145, h5, hc24, hlam, hphi, ht12, u1ehi3]
                  · linarith only [h135, h138, h4, hc12, hc25, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
                    · linarith only [h0, h150, h5, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                      · linarith only [h0, h152, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                        · linarith only [h149, h150, h154, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                          · linarith only [h156, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                            · linarith only [h154, h158, hc23, hlam, hphi, ht12, u1ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                              · linarith only [h0, h149, h160, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                                · linarith only [h0, h137, h149, h158, h162, h5, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h149, h162, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · linarith only [h149, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
            · rcases m.htr 0 2 5 (by decide) (by decide) with h167 | h167
              · linarith only [h167, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
                · linarith only [h166, h169, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h166, h171, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                      · linarith only [h0, h174, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                          · linarith only [h169, h177, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h180 | h180
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                                · linarith only [h169, h181, h2, hc24, hlam, hphi, ht12, u1ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                                  · linarith only [h0, h167, h181, h183, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                  · rcases h2bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h167, h173, h181, hc45, hlam, hphi, ht12, ht23, ht34, p185_1, u1ehi3]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h4, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h167, h179, h181, hc34, hc45, hlam, hphi, p185_1]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h167, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h0, hlam, p185_1]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h171, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h0, h167, h179, h181, hc34, hc45, hlam, hphi, p185_1]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h174, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht12, p185_1, u1ehi1]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht12, p185_1, u1ehi1]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      rcases p185_3 (m.d 0 2) (by simp) with h199 | h199
                                      · linarith only [h199, h4, hlam]
                                      · linarith only [h166, h199, hlam]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p185_1, u5ehi2]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h166, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h173, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h179, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h181, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h166, h2, hc25, hlam, hphi, ht12, p185_1, u1ehi3]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h173, hc25, hlam, hphi, ht12, p185_1, u1ehi3]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [h180, hlam, p185_0]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      rcases p185_3 (m.d 0 2) (by simp) with h211 | h211
                                      · linarith only [h167, h211, hlam]
                                      · linarith only [h166, h211, hlam]
                                    · have p185_0 := h185c.1
                                      have p185_1 := h185c.2.1
                                      have p185_2 := h185c.2.2.1
                                      have p185_3 := h185c.2.2.2
                                      linarith only [hlam, p185_0]
                              · linarith only [h166, h180, h2, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                            · linarith only [h166, h179, h2, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h171, h173, h176, hlam]
                    · linarith only [h166, h173, h4, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h219 | h219
              · linarith only [h219, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                  · linarith only [h0, h222, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
                    · linarith only [h0, h166, h224, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                      · linarith only [h0, h219, h226, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                          · linarith only [h1, h228, h229, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h166, h221, h229, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h2, h232, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h166, h221, h232, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                  · linarith only [h0, h235, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h166, h237, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                      · linarith only [h0, h219, h239, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h1, h241, h242, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                                · linarith only [h2, h221, h246, hc24, hlam, hphi, ht12, u1ehi3]
                                · linarith only [h0, h166, h246, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                              · linarith only [h0, h245, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h0, h1, h241, h244, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
                          · linarith only [h2, h221, h251, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                            · linarith only [h241, h253, hc23, hlam, hphi, ht12, u1ehi2]
                            · linarith only [h0, h253, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h259 | h259
    · linarith only [h0, h259, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h261 | h261
      · linarith only [h0, h261, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h263 | h263
        · linarith only [h0, h263, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
          · rcases m.htr 0 2 4 (by decide) (by decide) with h266 | h266
            · rcases m.htr 0 2 5 (by decide) (by decide) with h267 | h267
              · rcases m.htr 0 4 5 (by decide) (by decide) with h268 | h268
                · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                              · linarith only [h265, h275, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                                · linarith only [h274, h275, h277, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                                  · linarith only [h274, h275, h277, h279, hlam]
                                  · rcases h2bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      rcases p281_3 (m.d 0 2) (by simp) with h284 | h284
                                      · rcases p281_3 (m.d 1 2) (by simp) with h285 | h285
                                        · rcases p281_3 (m.d 2 3) (by simp) with h286 | h286
                                          · linarith only [h286, hlam, p281_0]
                                          · rcases p281_3 (m.d 2 4) (by simp) with h288 | h288
                                            · linarith only [h266, h288, hlam]
                                            · rcases p281_3 (m.d 2 5) (by simp) with h290 | h290
                                              · linarith only [h267, h290, hlam]
                                              · linarith only [h275, h290, hlam]
                                        · linarith only [h269, h285, hlam]
                                      · linarith only [h284, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      rcases p281_3 (m.d 0 2) (by simp) with h295 | h295
                                      · rcases p281_3 (m.d 1 2) (by simp) with h296 | h296
                                        · rcases p281_3 (m.d 2 3) (by simp) with h297 | h297
                                          · linarith only [h265, h297, hlam]
                                          · linarith only [h274, h297, hlam]
                                        · linarith only [h270, h296, hlam]
                                      · linarith only [h295, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p281_1, u5ehi2]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, p281_1, u1ehi0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      rcases p281_3 (m.d 0 2) (by simp) with h305 | h305
                                      · linarith only [h0, h305, hlam]
                                      · linarith only [h265, h305, hlam]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      rcases p281_3 (m.d 0 2) (by simp) with h308 | h308
                                      · linarith only [h0, h308, hlam]
                                      · linarith only [h266, h308, hlam]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p281_1, u5ehi2]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h265, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h269, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h261, h268, h269, h272, h275, h279, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h275, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h266, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h270, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h274, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h277, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h267, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h271, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, h267, h274, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      rcases p281_3 (m.d 0 2) (by simp) with h325 | h325
                                      · rcases p281_3 (m.d 1 2) (by simp) with h326 | h326
                                        · rcases p281_3 (m.d 2 3) (by simp) with h327 | h327
                                          · linarith only [h275, h327, hlam]
                                          · linarith only [h274, h327, hlam]
                                        · linarith only [h270, h326, hlam]
                                      · linarith only [h266, h325, hlam]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
                              · linarith only [h274, h333, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                                · linarith only [h0, h266, h335, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                                  · linarith only [h269, h272, h337, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · rcases h2bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h0, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h266, h268, h274, h337, hlam, p339_2]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      rcases p339_3 (m.d 0 2) (by simp) with h343 | h343
                                      · rcases p339_3 (m.d 1 2) (by simp) with h344 | h344
                                        · rcases p339_3 (m.d 2 3) (by simp) with h345 | h345
                                          · linarith only [h265, h345, hlam]
                                          · rcases p339_3 (m.d 2 4) (by simp) with h347 | h347
                                            · linarith only [h347, hlam, p339_0]
                                            · rcases p339_3 (m.d 2 5) (by simp) with h349 | h349
                                              · linarith only [h267, h349, hlam]
                                              · linarith only [h335, h349, hlam]
                                        · linarith only [h270, h344, hlam]
                                      · linarith only [h343, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht0b, ht5b, p339_1, u5ehi2]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, p339_1, u1ehi0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h0, h266, h268, h274, h337, hlam, p339_2]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      rcases p339_3 (m.d 0 2) (by simp) with h358 | h358
                                      · linarith only [h0, h358, hlam]
                                      · linarith only [h266, h358, hlam]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p339_1, u5ehi2]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h265, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h269, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h274, hlam, p339_1]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h333, hlam, p339_1]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h266, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h270, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h266, h268, h274, h337, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p339_1]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h335, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h267, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [h271, hlam, p339_0]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      rcases p339_3 (m.d 0 2) (by simp) with h374 | h374
                                      · rcases p339_3 (m.d 1 2) (by simp) with h375 | h375
                                        · rcases p339_3 (m.d 2 3) (by simp) with h376 | h376
                                          · linarith only [h333, h376, hlam]
                                          · rcases p339_3 (m.d 2 4) (by simp) with h378 | h378
                                            · linarith only [h335, h378, hlam]
                                            · linarith only [h274, h378, hlam]
                                        · linarith only [h269, h375, hlam]
                                      · linarith only [h265, h374, hlam]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      rcases p339_3 (m.d 0 2) (by simp) with h383 | h383
                                      · rcases p339_3 (m.d 1 2) (by simp) with h384 | h384
                                        · rcases p339_3 (m.d 2 3) (by simp) with h385 | h385
                                          · linarith only [h333, h385, hlam]
                                          · rcases p339_3 (m.d 2 4) (by simp) with h387 | h387
                                            · linarith only [h335, h387, hlam]
                                            · rcases p339_3 (m.d 2 5) (by simp) with h389 | h389
                                              · rcases h4bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h261, hlam, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h268, h333, h337, hlam, p339_1, p390_2]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  rcases p390_3 (m.d 0 4) (by simp) with h394 | h394
                                                  · rcases p390_3 (m.d 1 4) (by simp) with h395 | h395
                                                    · rcases p390_3 (m.d 2 4) (by simp) with h396 | h396
                                                      · linarith only [h266, h396, hlam]
                                                      · rcases p390_3 (m.d 3 4) (by simp) with h398 | h398
                                                        · linarith only [h398, hlam, p390_0]
                                                        · rcases p390_3 (m.d 4 5) (by simp) with h400 | h400
                                                          · linarith only [h268, h400, hlam]
                                                          · linarith only [h337, h400, hlam]
                                                    · linarith only [h272, h395, hlam]
                                                  · linarith only [h394, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h261, h269, h272, h333, h337, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p339_1, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h261, h269, h272, hc12, hlam, hphi, p390_1, u1ehi0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h261, h268, h333, h337, hlam, p339_1, p390_2]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  rcases p390_3 (m.d 0 4) (by simp) with h409 | h409
                                                  · linarith only [h261, h409, hlam]
                                                  · linarith only [h268, h337, h409, hlam]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h274, h333, h337, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p339_1, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h266, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h270, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h274, hlam, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h335, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h268, h337, hlam, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h272, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h268, h274, h337, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h337, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h268, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h273, hlam, p390_0]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  rcases p390_3 (m.d 0 4) (by simp) with h425 | h425
                                                  · rcases p390_3 (m.d 1 4) (by simp) with h426 | h426
                                                    · rcases p390_3 (m.d 2 4) (by simp) with h427 | h427
                                                      · linarith only [h427, hlam, p390_0]
                                                      · rcases p390_3 (m.d 3 4) (by simp) with h429 | h429
                                                        · linarith only [h337, h429, hlam]
                                                        · linarith only [h274, h429, hlam]
                                                    · linarith only [h270, h426, hlam]
                                                  · linarith only [h266, h425, hlam]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [h261, h268, h269, h272, h274, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p390_1]
                                                · have p390_0 := h390c.1
                                                  have p390_1 := h390c.2.1
                                                  have p390_2 := h390c.2.2.1
                                                  have p390_3 := h390c.2.2.2
                                                  linarith only [hlam, p390_0]
                                              · linarith only [h335, h389, hlam]
                                        · linarith only [h270, h384, hlam]
                                      · linarith only [h266, h383, hlam]
                                    · have p339_0 := h339c.1
                                      have p339_1 := h339c.2.1
                                      have p339_2 := h339c.2.2.1
                                      have p339_3 := h339c.2.2.2
                                      linarith only [hlam, p339_0]
                          · linarith only [h261, h268, h273, hlam]
                        · linarith only [h259, h272, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h271, hc25, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h266, h268, h270, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h266, h268, h269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h448 | h448
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                          · linarith only [h261, h268, h448, h449, hc13, hlam, hphi, u1ehi0]
                          · linarith only [h261, h449, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                        · linarith only [h259, h448, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h267, h447, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h0, h267, h446, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h265, h445, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
                · linarith only [h266, h267, h456, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                      · linarith only [h0, h267, h460, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h460, hc25, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h259, h266, h458, h459, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h265, h267, h458, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
              · linarith only [h266, h465, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                    · linarith only [h0, h266, h469, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h469, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h265, h465, h468, hc25, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h474 | h474
                    · linarith only [h259, h265, h266, h474, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h474, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h265, h266, h467, h473, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h478 | h478
            · rcases m.htr 0 2 5 (by decide) (by decide) with h479 | h479
              · linarith only [h265, h479, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                · linarith only [h265, h478, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
                  · linarith only [h0, h265, h483, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h483, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h486 | h486
              · linarith only [h478, h486, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                  · linarith only [h0, h265, h489, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h489, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                  · linarith only [h0, h265, h492, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h492, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
