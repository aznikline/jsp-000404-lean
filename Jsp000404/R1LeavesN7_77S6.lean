import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_24_L_R_M_LI (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
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
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h13, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h12, h8, hc14, hlam, hphi, u4elo0]
                        · linarith only [h11, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · linarith only [h10, h4, h9, hlam, hphi, ht34, u3ehi2, u4elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                            · linarith only [h0, h19, h22, h3, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h19, h20, h22, h9, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h20, h21, h8, hlam, hphi, ht34, u3ehi3, u4elo0]
                        · linarith only [h20, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                                  · rcases h4bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h27, h32, hlam, hphi, ht34, p33_1, u3ehi4, u4elo0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h19, hc12, hlam, hphi, ht23, ht34, p33_1, u4elo0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h32, hlam, hphi, ht34, p33_1, u3ehi4, u4elo0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      rcases p33_3 (m.d 0 4) (by simp) with h38 | h38
                                      · rcases p33_3 (m.d 1 4) (by simp) with h39 | h39
                                        · linarith only [h2, h39, hlam]
                                        · linarith only [h28, h39, hlam]
                                      · linarith only [h38, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h2, hlam, p33_1]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h19, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h32, hlam, hphi, ht34, p33_1, u3ehi4, u4elo1]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      rcases p33_3 (m.d 0 4) (by simp) with h47 | h47
                                      · rcases p33_3 (m.d 1 4) (by simp) with h48 | h48
                                        · rcases p33_3 (m.d 2 4) (by simp) with h49 | h49
                                          · rcases p33_3 (m.d 3 4) (by simp) with h50 | h50
                                            · linarith only [h27, h50, hlam]
                                            · linarith only [h32, h50, hlam]
                                          · linarith only [h31, h49, hlam]
                                        · linarith only [h48, hlam, p33_0]
                                      · linarith only [h47, h8, hlam]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h4, hlam, p33_1]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h4, hc14, hlam, hphi, p33_1, u4elo0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h32, h4, hlam, hphi, ht34, p33_1, u3ehi4, u4elo0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      rcases p33_3 (m.d 0 4) (by simp) with h60 | h60
                                      · rcases p33_3 (m.d 1 4) (by simp) with h61 | h61
                                        · linarith only [h19, h61, hlam]
                                        · linarith only [h28, h61, hlam]
                                      · linarith only [h60, h8, hlam]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h6, hlam, p33_1]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h27, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h29, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h0, h27, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p33_1]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h8, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h28, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h31, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [h32, hlam, p33_0]
                                    · have p33_0 := h33c.1
                                      have p33_1 := h33c.2.1
                                      have p33_2 := h33c.2.2.1
                                      have p33_3 := h33c.2.2.2
                                      linarith only [hlam, p33_0]
                                  · linarith only [h32, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h28, h31, hc24, hlam, hphi, u4elo1]
                              · linarith only [h30, h7, h8, h9, hlam, hphi, ht34, u3ehi1, u4elo0]
                            · linarith only [h27, h29, h9, hlam]
                          · linarith only [h28, h8, hc14, hlam, hphi, u4elo0]
                        · linarith only [h27, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · linarith only [h6, h8, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · linarith only [h6, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
              · rcases m.htr 0 3 5 (by decide) (by decide) with h85 | h85
                · linarith only [h3, h5, h85, hlam]
                · linarith only [h84, h85, hc35, hlam, hphi, u3ehi3]
              · linarith only [h84, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h3, h4, hlam, hphi, ht34, u3ehi2, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h90 | h90
          · rcases m.htr 0 2 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 0 3 4 (by decide) (by decide) with h92 | h92
              · rcases m.htr 0 3 5 (by decide) (by decide) with h93 | h93
                · rcases m.htr 0 4 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                    · linarith only [h0, h3, h90, h93, h94, h95, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                                  · rcases h4bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h101, h102, h97, hlam, hphi, ht34, p104_1, u3ehi4, u4elo0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h101, h102, hlam, hphi, ht34, p104_1, u3ehi4, u4elo0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hc34, hlam, hphi, p104_1, u4elo0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      rcases p104_3 (m.d 0 4) (by simp) with h109 | h109
                                      · rcases p104_3 (m.d 1 4) (by simp) with h110 | h110
                                        · linarith only [h110, h2, hlam]
                                        · linarith only [h110, h99, hlam]
                                      · linarith only [h109, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h2, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h101, h102, hlam, hphi, ht34, p104_1, u3ehi4, u4elo1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h103, h2, hlam, hphi, ht34, p104_1, u3ehi4, u4elo0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      rcases p104_3 (m.d 0 4) (by simp) with h118 | h118
                                      · rcases p104_3 (m.d 1 4) (by simp) with h119 | h119
                                        · rcases p104_3 (m.d 2 4) (by simp) with h120 | h120
                                          · linarith only [h120, h97, hlam]
                                          · linarith only [h102, h120, hlam]
                                        · linarith only [h119, hlam, p104_0]
                                      · linarith only [h118, h94, hlam]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h90, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h97, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h103, h3, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p104_1, u3ehi4]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h3, h97, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h92, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h98, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h100, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h1, h98, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h94, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h99, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h102, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h103, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                  · linarith only [h103, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h102, h2, h99, hc24, hlam, hphi, u4elo0]
                              · linarith only [h0, h100, h101, h3, h97, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h100, h3, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h94, h99, hc14, hlam, hphi, u4elo0]
                        · linarith only [h98, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · linarith only [h3, h90, h97, hc12, hc23, hlam, hphi]
                  · linarith only [h92, h94, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h92, h93, hc35, hlam, hphi, u3ehi3]
              · linarith only [h92, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
              · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
                · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                  · linarith only [h152, h90, h91, hlam]
                  · linarith only [h150, h152, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h150, h151, hc35, hlam, hphi, u3ehi3]
              · linarith only [h150, hlam, hphi, ht34, u3ehi0, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
            · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
              · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
                · linarith only [h157, h159, h90, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h158, h159, hc35, hlam, hphi, u3ehi3]
              · linarith only [h158, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                    · linarith only [h0, h166, h3, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                      · linarith only [h0, h168, h90, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                                  · rcases h4bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h170, h175, hlam, hphi, ht34, p176_1, u3ehi4, u4elo0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h90, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h175, h90, hlam, hphi, ht34, p176_1, u3ehi4, u4elo2]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      rcases p176_3 (m.d 0 4) (by simp) with h181 | h181
                                      · rcases p176_3 (m.d 1 4) (by simp) with h182 | h182
                                        · linarith only [h182, h2, hlam]
                                        · linarith only [h171, h182, hlam]
                                      · linarith only [h181, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h2, hlam, p176_1]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h168, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h175, hlam, hphi, ht34, p176_1, u3ehi4, u4elo1]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      rcases p176_3 (m.d 0 4) (by simp) with h190 | h190
                                      · rcases p176_3 (m.d 1 4) (by simp) with h191 | h191
                                        · rcases p176_3 (m.d 2 4) (by simp) with h192 | h192
                                          · rcases p176_3 (m.d 3 4) (by simp) with h193 | h193
                                            · linarith only [h170, h193, hlam]
                                            · linarith only [h175, h193, hlam]
                                          · linarith only [h174, h192, hlam]
                                        · linarith only [h191, hlam, p176_0]
                                      · linarith only [h165, h190, hlam]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hc04, hlam, hphi, p176_1, u4elo2]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hc14, hlam, hphi, p176_1, u4elo2]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h175, hlam, hphi, ht34, p176_1, u3ehi4, u4elo2]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      rcases p176_3 (m.d 0 4) (by simp) with h203 | h203
                                      · linarith only [h203, h90, hlam]
                                      · linarith only [h165, h203, hlam]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h163, hlam, p176_1]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h170, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h172, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h1, h170, hc01, hc45, hlam, hphi, ht0b, ht5b, p176_1]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h165, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h171, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h174, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [h175, hlam, p176_0]
                                    · have p176_0 := h176c.1
                                      have p176_1 := h176c.2.1
                                      have p176_2 := h176c.2.2.1
                                      have p176_3 := h176c.2.2.2
                                      linarith only [hlam, p176_0]
                                  · linarith only [h175, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h171, h174, h2, h90, hlam]
                              · linarith only [h163, h173, h3, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1, h170, h172, h3, hlam]
                          · linarith only [h165, h171, h90, hc14, hlam, hphi, u4elo2]
                        · linarith only [h170, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · linarith only [h163, h165, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h163, h164, hc35, hlam, hphi, u3ehi3]
              · linarith only [h163, hlam, hphi, ht34, u3ehi0, u4elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h226 | h226
      · rcases m.htr 0 2 3 (by decide) (by decide) with h227 | h227
        · linarith only [h0, h1, h227, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
          · rcases m.htr 0 2 5 (by decide) (by decide) with h230 | h230
            · rcases m.htr 0 3 4 (by decide) (by decide) with h231 | h231
              · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h227, h229, h234, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                            · linarith only [h0, h1, h234, h236, h239, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h234, h236, h237, h239, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h237, h238, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h0, h1, h237, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h229, h234, h236, hc12, hc23, hlam, hphi]
                  · linarith only [h231, h233, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h231, h232, hc35, hlam, hphi, u3ehi3]
              · linarith only [h231, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h248 | h248
              · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
                  · linarith only [h229, h230, h250, hlam]
                  · linarith only [h248, h250, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h248, h249, hc35, hlam, hphi, u3ehi3]
              · linarith only [h248, hlam, hphi, ht34, u3ehi0, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h255 | h255
            · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
              · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                · linarith only [h229, h255, h257, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h256, h257, hc35, hlam, hphi, u3ehi3]
              · linarith only [h256, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h261 | h261
              · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
                · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h1, h264, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h229, h266, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h268 | h268
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                                  · rcases h4bigk with h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h268, h273, hlam, hphi, ht34, p274_1, u3ehi4, u4elo0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h229, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h229, h273, hlam, hphi, ht34, p274_1, u3ehi4, u4elo2]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      rcases p274_3 (m.d 0 4) (by simp) with h279 | h279
                                      · rcases p274_3 (m.d 1 4) (by simp) with h280 | h280
                                        · linarith only [h226, h280, hlam]
                                        · linarith only [h269, h280, hlam]
                                      · linarith only [h279, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h226, hlam, p274_1]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h266, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h226, h273, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p274_1, u3ehi4]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h1, h226, h264, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p274_1]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hc04, hlam, hphi, p274_1, u4elo2]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hc14, hlam, hphi, p274_1, u4elo2]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h273, hlam, hphi, ht34, p274_1, u3ehi4, u4elo2]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      rcases p274_3 (m.d 0 4) (by simp) with h293 | h293
                                      · linarith only [h229, h293, hlam]
                                      · linarith only [h263, h293, hlam]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h261, hlam, p274_1]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h268, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h270, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h1, h226, h264, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p274_1]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h263, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h269, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h272, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [h273, hlam, p274_0]
                                    · have p274_0 := h274c.1
                                      have p274_1 := h274c.2.1
                                      have p274_2 := h274c.2.2.1
                                      have p274_3 := h274c.2.2.2
                                      linarith only [hlam, p274_0]
                                  · linarith only [h273, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h1, h226, h264, h269, h272, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h1, h226, h264, h269, h271, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h226, h264, h268, h270, hlam]
                          · linarith only [h268, h269, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h1, h268, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h261, h263, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h261, h262, hc35, hlam, hphi, u3ehi3]
              · linarith only [h261, hlam, hphi, ht34, u3ehi0, u4elo3]
      · linarith only [h0, h226, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h316 | h316
    · rcases m.htr 0 1 4 (by decide) (by decide) with h317 | h317
      · rcases m.htr 0 2 3 (by decide) (by decide) with h318 | h318
        · rcases m.htr 0 2 4 (by decide) (by decide) with h319 | h319
          · rcases m.htr 0 2 5 (by decide) (by decide) with h320 | h320
            · rcases m.htr 0 3 4 (by decide) (by decide) with h321 | h321
              · rcases m.htr 0 3 5 (by decide) (by decide) with h322 | h322
                · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                        · linarith only [h0, h316, h326, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h326, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · linarith only [h0, h325, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h316, h321, h324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h321, h323, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h321, h322, hc35, hlam, hphi, u3ehi3]
              · linarith only [h321, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h334 | h334
              · rcases m.htr 0 3 5 (by decide) (by decide) with h335 | h335
                · linarith only [h0, h316, h320, h335, hlam]
                · linarith only [h334, h335, hc35, hlam, hphi, u3ehi3]
              · linarith only [h334, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h0, h316, h319, hlam, hphi, ht34, u3ehi1, u4elo2]
        · linarith only [h0, h316, h318, hlam]
      · linarith only [h316, h317, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h342 | h342
      · rcases m.htr 0 2 3 (by decide) (by decide) with h343 | h343
        · rcases m.htr 0 2 4 (by decide) (by decide) with h344 | h344
          · rcases m.htr 0 2 5 (by decide) (by decide) with h345 | h345
            · rcases m.htr 0 3 4 (by decide) (by decide) with h346 | h346
              · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
                · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                                  · rcases h4bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h350, h354, h355, hlam, hphi, ht34, p357_1, u3ehi4, u4elo0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h354, h355, hlam, hphi, ht34, p357_1, u3ehi4, u4elo0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h356, hlam, hphi, ht34, p357_1, u3ehi4, u4elo0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      rcases p357_3 (m.d 0 4) (by simp) with h362 | h362
                                      · rcases p357_3 (m.d 1 4) (by simp) with h363 | h363
                                        · linarith only [h342, h363, hlam]
                                        · linarith only [h352, h363, hlam]
                                      · linarith only [h362, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h342, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h342, h354, h355, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p357_1, u3ehi4]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h316, h342, h349, h356, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p357_1, u3ehi4]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h316, h342, h349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h344, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h350, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h356, hlam, hphi, ht34, p357_1, u3ehi4, u4elo2]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h316, h342, h349, h350, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h346, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h351, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h353, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h343, h353, hc02, hc45, hlam, hphi, ht0b, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h348, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h352, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h355, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h356, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                  · linarith only [h356, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h316, h342, h349, h352, h355, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h347, h348, h354, hlam, hphi, ht34, u3ehi2, u4elo0]
                            · linarith only [h353, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h351, h352, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h316, h351, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h316, h342, h347, h348, h349, h350, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h0, h342, h343, h347, h348, h349, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h346, h348, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h346, h347, hc35, hlam, hphi, u3ehi3]
              · linarith only [h346, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h398 | h398
              · rcases m.htr 0 3 5 (by decide) (by decide) with h399 | h399
                · linarith only [h343, h345, h399, hlam]
                · linarith only [h398, h399, hc35, hlam, hphi, u3ehi3]
              · linarith only [h398, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h0, h342, h344, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
          · rcases m.htr 0 2 5 (by decide) (by decide) with h405 | h405
            · rcases m.htr 0 3 4 (by decide) (by decide) with h406 | h406
              · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
                · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h411 | h411
                        · linarith only [h0, h342, h343, h409, h411, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h342, h343, h406, h409, h411, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h342, h343, h407, h408, h409, h410, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h415 | h415
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
                        · linarith only [h0, h342, h409, h416, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h316, h416, hlam, hphi, ht34, u3ehi0, u4elo3]
                      · linarith only [h0, h415, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h406, h408, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h406, h407, hc35, hlam, hphi, u3ehi3]
              · linarith only [h406, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
              · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
                · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
                  · linarith only [h0, h342, h405, h425, hlam]
                  · linarith only [h423, h425, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h423, h424, hc35, hlam, hphi, u3ehi3]
              · linarith only [h423, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h0, h342, h404, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h431 | h431
        · rcases m.htr 0 2 4 (by decide) (by decide) with h432 | h432
          · rcases m.htr 0 2 5 (by decide) (by decide) with h433 | h433
            · rcases m.htr 0 3 4 (by decide) (by decide) with h434 | h434
              · rcases m.htr 0 3 5 (by decide) (by decide) with h435 | h435
                · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h439 | h439
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h440 | h440
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h441 | h441
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h443 | h443
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
                                  · rcases h4bigk with h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h342, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hc24, hlam, hphi, p445_1, u4elo0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h342, h444, hlam, hphi, ht34, p445_1, u3ehi4, u4elo1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      rcases p445_3 (m.d 0 4) (by simp) with h450 | h450
                                      · rcases p445_3 (m.d 1 4) (by simp) with h451 | h451
                                        · rcases p445_3 (m.d 2 4) (by simp) with h452 | h452
                                          · linarith only [h432, h452, hlam]
                                          · linarith only [h443, h452, hlam]
                                        · linarith only [h440, h451, hlam]
                                      · linarith only [h450, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hc04, hlam, hphi, p445_1, u4elo1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h441, h444, hlam, hphi, ht34, p445_1, u3ehi4, u4elo1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h444, hlam, hphi, ht34, p445_1, u3ehi4, u4elo1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      rcases p445_3 (m.d 0 4) (by simp) with h461 | h461
                                      · linarith only [h342, h461, hlam]
                                      · linarith only [h436, h461, hlam]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h432, hlam, p445_1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h438, hlam, p445_1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h432, h444, hlam, hphi, ht34, p445_1, u3ehi4, u4elo0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      rcases p445_3 (m.d 0 4) (by simp) with h468 | h468
                                      · rcases p445_3 (m.d 1 4) (by simp) with h469 | h469
                                        · rcases p445_3 (m.d 2 4) (by simp) with h470 | h470
                                          · rcases p445_3 (m.d 3 4) (by simp) with h471 | h471
                                            · linarith only [h441, h471, hlam]
                                            · linarith only [h444, h471, hlam]
                                          · linarith only [h470, hlam, p445_0]
                                        · linarith only [h440, h469, hlam]
                                      · linarith only [h436, h468, hlam]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h434, hlam, p445_1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h439, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h441, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h0, h431, h441, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p445_1]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h436, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h440, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h443, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [h444, hlam, p445_0]
                                    · have p445_0 := h445c.1
                                      have p445_1 := h445c.2.1
                                      have p445_2 := h445c.2.2.1
                                      have p445_3 := h445c.2.2.2
                                      linarith only [hlam, p445_0]
                                  · linarith only [h444, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h342, h436, h443, hc24, hlam, hphi, u4elo1]
                              · linarith only [h441, h442, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h441, hlam, hphi, ht34, u3ehi2, u4elo3]
                          · linarith only [h342, h436, h440, hlam]
                        · linarith only [h316, h434, h439, hlam]
                      · linarith only [h0, h431, h435, h438, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h0, h431, h437, hlam]
                  · linarith only [h434, h436, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h434, h435, hc35, hlam, hphi, u3ehi3]
              · linarith only [h434, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h498 | h498
              · rcases m.htr 0 3 5 (by decide) (by decide) with h499 | h499
                · linarith only [h431, h433, h499, hlam]
                · linarith only [h498, h499, hc35, hlam, hphi, u3ehi3]
              · linarith only [h498, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h431, h432, hlam, hphi, ht34, u3ehi2, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h504 | h504
          · rcases m.htr 0 2 5 (by decide) (by decide) with h505 | h505
            · rcases m.htr 0 3 4 (by decide) (by decide) with h506 | h506
              · rcases m.htr 0 3 5 (by decide) (by decide) with h507 | h507
                · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h510 | h510
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h511 | h511
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                            · linarith only [h431, h504, h509, h513, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h431, h504, h506, h513, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h431, h504, h508, h509, h512, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h431, h504, h506, h509, h511, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h431, h509, h510, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h520 | h520
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h523 | h523
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h524 | h524
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h525 | h525
                                  · rcases h4bigk with h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c | h526c
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h342, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h523, h524, hlam, hphi, ht34, p526_1, u3ehi4, u4elo0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h525, hlam, hphi, ht34, p526_1, u3ehi4, u4elo0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      rcases p526_3 (m.d 0 4) (by simp) with h531 | h531
                                      · rcases p526_3 (m.d 1 4) (by simp) with h532 | h532
                                        · rcases p526_3 (m.d 2 4) (by simp) with h533 | h533
                                          · linarith only [h504, h533, hlam]
                                          · linarith only [h524, h533, hlam]
                                        · linarith only [h521, h532, hlam]
                                      · linarith only [h531, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hc04, hlam, hphi, p526_1, u4elo1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h523, h524, hlam, hphi, ht34, p526_1, u3ehi4, u4elo1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h525, hlam, hphi, ht34, p526_1, u3ehi4, u4elo1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      rcases p526_3 (m.d 0 4) (by simp) with h542 | h542
                                      · linarith only [h342, h542, hlam]
                                      · linarith only [h508, h542, hlam]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h504, hlam, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h519, hlam, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h0, h504, h509, h525, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p526_1, u3ehi4]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h0, h504, h509, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h506, hlam, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h520, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h522, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h0, h504, h509, h522, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p526_1]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h508, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h521, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h524, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [h525, hlam, p526_0]
                                    · have p526_0 := h526c.1
                                      have p526_1 := h526c.2.1
                                      have p526_2 := h526c.2.2.1
                                      have p526_3 := h526c.2.2.2
                                      linarith only [hlam, p526_0]
                                  · linarith only [h525, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h342, h508, h524, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h509, h523, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h504, h506, h509, h522, hlam]
                          · linarith only [h0, h342, h504, h508, h521, hc01, hc12, hlam, hphi]
                        · linarith only [h316, h342, h506, h520, hlam, hphi, ht34, u3ehi0, u4elo1]
                      · linarith only [h0, h504, h519, hlam]
                  · linarith only [h506, h508, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h506, h507, hc35, hlam, hphi, u3ehi3]
              · linarith only [h506, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h570 | h570
              · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                · rcases m.htr 0 4 5 (by decide) (by decide) with h572 | h572
                  · linarith only [h504, h505, h572, hlam]
                  · linarith only [h570, h572, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h570, h571, hc35, hlam, hphi, u3ehi3]
              · linarith only [h570, hlam, hphi, ht34, u3ehi0, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h577 | h577
            · rcases m.htr 0 3 4 (by decide) (by decide) with h578 | h578
              · rcases m.htr 0 3 5 (by decide) (by decide) with h579 | h579
                · linarith only [h504, h577, h579, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h578, h579, hc35, hlam, hphi, u3ehi3]
              · linarith only [h578, hlam, hphi, ht34, u3ehi0, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h583 | h583
              · rcases m.htr 0 3 5 (by decide) (by decide) with h584 | h584
                · rcases m.htr 0 4 5 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h587 | h587
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h589 | h589
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h590 | h590
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h592 | h592
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h593 | h593
                                  · rcases h4bigk with h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h342, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h504, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h593, hlam, hphi, ht34, p594_1, u3ehi4, u4elo0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      rcases p594_3 (m.d 0 4) (by simp) with h599 | h599
                                      · rcases p594_3 (m.d 1 4) (by simp) with h600 | h600
                                        · rcases p594_3 (m.d 2 4) (by simp) with h601 | h601
                                          · rcases p594_3 (m.d 3 4) (by simp) with h602 | h602
                                            · linarith only [h583, h602, hlam]
                                            · linarith only [h593, h602, hlam]
                                          · linarith only [h592, h601, hlam]
                                        · linarith only [h589, h600, hlam]
                                      · linarith only [h599, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [hc04, hlam, hphi, p594_1, u4elo1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h577, h592, hc02, hlam, hphi, ht23, ht34, p594_1, u4elo1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h593, hlam, hphi, ht34, p594_1, u3ehi4, u4elo1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      rcases p594_3 (m.d 0 4) (by simp) with h612 | h612
                                      · linarith only [h342, h612, hlam]
                                      · linarith only [h585, h612, hlam]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h583, h593, hlam, hphi, ht34, p594_1, u3ehi4, u4elo2]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h587, hlam, p594_1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h587, h593, hlam, hphi, ht34, p594_1, u3ehi4, u4elo1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      rcases p594_3 (m.d 0 4) (by simp) with h619 | h619
                                      · linarith only [h504, h619, hlam]
                                      · linarith only [h585, h619, hlam]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h583, hlam, p594_1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h588, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h590, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h431, h583, h586, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p594_1]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h585, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h589, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h592, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [h593, hlam, p594_0]
                                    · have p594_0 := h594c.1
                                      have p594_1 := h594c.2.1
                                      have p594_2 := h594c.2.2.1
                                      have p594_3 := h594c.2.2.2
                                      linarith only [hlam, p594_0]
                                  · linarith only [h593, hlam, hphi, ht34, u3ehi3, u4elo4]
                                · linarith only [h585, h592, hc24, hlam, hphi, u4elo0]
                              · linarith only [h431, h583, h591, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h431, h583, h590, hlam]
                          · linarith only [h504, h585, h587, h589, hlam]
                        · linarith only [h431, h583, h586, h588, hlam]
                      · linarith only [h431, h583, h586, h587, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h639 | h639
                      · linarith only [h0, h504, h586, h639, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h639, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h583, h585, hlam, hphi, ht34, u3ehi3, u4elo4]
                · linarith only [h583, h584, hc35, hlam, hphi, u3ehi3]
              · linarith only [h583, hlam, hphi, ht34, u3ehi0, u4elo3]

end R2N4
