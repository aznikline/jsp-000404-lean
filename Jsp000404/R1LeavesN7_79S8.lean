import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_14_25_L_0_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                · linarith only [h6, h7, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h3, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h1, h13, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h13, h16, h3, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h16, h3, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h12, h13, h15, h3, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                    · linarith only [h1, h20, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h12, h20, h23, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h23, h3, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h26, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                        · linarith only [h0, h26, h3, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h30, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                · linarith only [h0, h29, h30, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h29, h3, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · linarith only [h3, h4, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
          · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
            · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
              · linarith only [h3, h35, h37, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                · linarith only [h0, h39, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                · linarith only [h3, h35, h39, hc12, hc24, hlam, hphi]
            · linarith only [h3, h35, h36, hlam, hphi, u5ehi7, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
              · linarith only [h3, h43, h44, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h35, h46, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h1, h49, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                          · linarith only [h44, h48, h49, h53, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · rcases h4bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              rcases p55_3 (m.d 0 4) (by simp) with h57 | h57
                              · rcases p55_3 (m.d 1 4) (by simp) with h58 | h58
                                · linarith only [h1, h58, hlam]
                                · rcases p55_3 (m.d 2 4) (by simp) with h60 | h60
                                  · rcases p55_3 (m.d 3 4) (by simp) with h61 | h61
                                    · linarith only [h43, h48, h49, h61, hlam]
                                    · rcases p55_3 (m.d 4 5) (by simp) with h63 | h63
                                      · linarith only [h43, h63, hlam]
                                      · linarith only [h49, h63, hlam]
                                  · linarith only [h44, h60, hlam]
                              · linarith only [h1, h57, hlam]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h3, hlam, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              rcases p55_3 (m.d 0 4) (by simp) with h69 | h69
                              · rcases p55_3 (m.d 1 4) (by simp) with h70 | h70
                                · linarith only [h1, h70, hlam]
                                · linarith only [h48, h70, hlam]
                              · linarith only [h69, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h3, h44, h49, h51, hc12, hc23, hlam, hphi, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h1, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h44, hlam, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h49, hc34, hc45, hlam, hphi, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h49, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h43, h49, h51, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              rcases p55_3 (m.d 0 4) (by simp) with h81 | h81
                              · linarith only [h3, h81, hlam]
                              · linarith only [h1, h81, hlam]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              rcases p55_3 (m.d 0 4) (by simp) with h85 | h85
                              · linarith only [h3, h85, hlam]
                              · linarith only [h43, h44, h48, h49, h85, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h44, h49, h51, hc12, hc23, hlam, hphi, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h43, h48, h49, hlam, p55_1]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h48, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h51, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h53, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h43, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h44, hc12, hlam, hphi, ht23, ht34, ht45, p55_1, u5elo4]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h52, hlam, p55_0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [h1, h43, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p55_1, u1elo0]
                            · have p55_0 := h55c.1
                              have p55_1 := h55c.2.1
                              have p55_2 := h55c.2.2.1
                              have p55_3 := h55c.2.2.2
                              linarith only [hlam, p55_0]
                        · linarith only [h1, h3, h43, h52, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1, h43, h48, h49, h51, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                    · linarith only [h1, h101, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                          · linarith only [h101, h103, h105, h44, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h105, h43, h48, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h104, h3, h43, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h110 | h110
                          · rcases h4bigk with h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              rcases p111_3 (m.d 0 4) (by simp) with h113 | h113
                              · rcases p111_3 (m.d 1 4) (by simp) with h114 | h114
                                · linarith only [h1, h114, hlam]
                                · rcases p111_3 (m.d 2 4) (by simp) with h116 | h116
                                  · rcases p111_3 (m.d 3 4) (by simp) with h117 | h117
                                    · rcases p111_3 (m.d 4 5) (by simp) with h118 | h118
                                      · linarith only [h118, h43, hlam]
                                      · linarith only [h101, h118, hlam]
                                    · linarith only [h117, h48, hlam]
                                  · linarith only [h116, h44, hlam]
                              · linarith only [h1, h113, hlam]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h3, hlam, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h103, h3, hlam, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h1, h101, h44, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p111_1, u1elo0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h1, hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h44, hlam, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h48, hlam, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h101, hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h101, h103, h43, h44, hc12, hc34, hlam, hphi, ht23, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              rcases p111_3 (m.d 0 4) (by simp) with h133 | h133
                              · linarith only [h133, h3, hlam]
                              · linarith only [h1, h133, hlam]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h103, hlam, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h101, h103, h44, hc12, hc34, hlam, hphi, ht23, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h101, h43, h44, hc12, hc34, hlam, hphi, ht23, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              rcases p111_3 (m.d 0 4) (by simp) with h140 | h140
                              · linarith only [h103, h140, h3, hlam]
                              · linarith only [h1, h140, hlam]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h101, h44, hc12, hc34, hlam, hphi, ht23, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h43, hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h3, h43, h44, hc12, hc24, hlam, hphi, p111_1]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h109, hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [h110, hlam, p111_0]
                            · have p111_0 := h111c.1
                              have p111_1 := h111c.2.1
                              have p111_2 := h111c.2.2.1
                              have p111_3 := h111c.2.2.2
                              linarith only [hlam, p111_0]
                          · linarith only [h1, h103, h110, h43, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h109, h3, h43, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
              · linarith only [h0, h153, h3, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                · linarith only [h0, h155, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                    · linarith only [h0, h1, h158, h3, h43, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                          · linarith only [h157, h162, h43, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi5]
                          · rcases h4bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h160, h161, h43, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p164_1]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h3, hlam, p164_1]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h161, h43, hc34, hlam, hphi, ht45, p164_1, u5elo2]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h43, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h1, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h153, hlam, p164_1]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h1, h161, h43, hc34, hlam, hphi, ht45, p164_1, u5elo2]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h158, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              rcases p164_3 (m.d 0 4) (by simp) with h175 | h175
                              · linarith only [h175, h3, hlam]
                              · rcases p164_3 (m.d 1 4) (by simp) with h177 | h177
                                · linarith only [h153, h177, hlam]
                                · rcases p164_3 (m.d 2 4) (by simp) with h179 | h179
                                  · rcases p164_3 (m.d 3 4) (by simp) with h180 | h180
                                    · linarith only [h160, h180, hlam]
                                    · rcases p164_3 (m.d 4 5) (by simp) with h182 | h182
                                      · linarith only [h161, h182, hlam]
                                      · linarith only [h182, h43, hlam]
                                  · linarith only [h179, h3, hlam]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              rcases p164_3 (m.d 0 4) (by simp) with h186 | h186
                              · linarith only [h186, h3, hlam]
                              · linarith only [h1, h186, hlam]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              rcases p164_3 (m.d 0 4) (by simp) with h190 | h190
                              · linarith only [h190, h3, hlam]
                              · linarith only [h1, h157, h190, hlam]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h1, h153, h160, h43, hc12, hc23, hlam, hphi, p164_1]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h1, h157, hlam, p164_1]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h157, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h160, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h162, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h1, h153, h161, hc12, hlam, hphi, ht23, ht34, ht45, p164_1, u5elo2]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h153, h161, hc12, hlam, hphi, ht23, ht34, ht45, p164_1, u5elo2]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h161, hlam, p164_0]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [h161, hc34, hlam, hphi, ht45, p164_1, u5elo2]
                            · have p164_0 := h164c.1
                              have p164_1 := h164c.2.1
                              have p164_2 := h164c.2.2.1
                              have p164_3 := h164c.2.2.2
                              linarith only [hlam, p164_0]
                        · linarith only [h0, h161, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1, h157, h160, h43, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h206 | h206
                    · linarith only [h1, h206, h43, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                          · linarith only [h0, h208, h210, h3, h43, hc12, hc23, hlam, hphi]
                          · linarith only [h157, h209, h210, hc13, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h209, h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h215 | h215
                          · rcases h4bigk with h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h214, h43, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h3, hlam, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h208, h214, h43, hc23, hlam, hphi, ht34, ht45, p216_1, u5elo2]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h43, hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h1, hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h153, hlam, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h157, hlam, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h206, hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              rcases p216_3 (m.d 0 4) (by simp) with h227 | h227
                              · linarith only [h227, h3, hlam]
                              · rcases p216_3 (m.d 1 4) (by simp) with h229 | h229
                                · linarith only [h153, h229, hlam]
                                · rcases p216_3 (m.d 2 4) (by simp) with h231 | h231
                                  · rcases p216_3 (m.d 3 4) (by simp) with h232 | h232
                                    · rcases p216_3 (m.d 4 5) (by simp) with h233 | h233
                                      · linarith only [h214, h233, hlam]
                                      · linarith only [h233, h43, hlam]
                                    · linarith only [h208, h232, hlam, p216_1]
                                  · linarith only [h231, h3, hlam]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              rcases p216_3 (m.d 0 4) (by simp) with h238 | h238
                              · linarith only [h238, h3, hlam]
                              · linarith only [h1, h238, hlam]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h208, hlam, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h1, h153, h43, hc12, hc24, hlam, hphi, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              rcases p216_3 (m.d 0 4) (by simp) with h244 | h244
                              · linarith only [h244, hlam, p216_0]
                              · rcases p216_3 (m.d 1 4) (by simp) with h246 | h246
                                · linarith only [h157, h246, hlam]
                                · rcases p216_3 (m.d 2 4) (by simp) with h248 | h248
                                  · linarith only [h208, h248, hlam]
                                  · linarith only [h248, h3, hlam]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              rcases p216_3 (m.d 0 4) (by simp) with h251 | h251
                              · linarith only [h0, h208, h214, h251, h3, h43, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                              · linarith only [h1, h251, hlam]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h0, h3, h43, hc12, hc34, hlam, hphi, ht23, p216_1]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h1, h214, hc14, hlam, hphi, ht45, p216_1, u5elo2]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h153, h214, hc12, hlam, hphi, ht23, ht34, ht45, p216_1, u5elo2]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h214, hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [h215, hlam, p216_0]
                            · have p216_0 := h216c.1
                              have p216_1 := h216c.2.1
                              have p216_2 := h216c.2.2.1
                              have p216_3 := h216c.2.2.2
                              linarith only [hlam, p216_0]
                          · linarith only [h157, h214, h215, hc13, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h0, h214, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h265 | h265
      · linarith only [h1, h265, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
      · linarith only [h0, h265, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h268 | h268
    · rcases m.htr 0 1 5 (by decide) (by decide) with h269 | h269
      · linarith only [h0, h269, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
      · linarith only [h268, h269, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h272 | h272
      · linarith only [h268, h272, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h274 | h274
        · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
          · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
            · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
              · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h0, h274, h282, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                          · linarith only [h281, h282, h284, hlam]
                          · rcases h4bigk with h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h268, hlam, p286_1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              rcases p286_3 (m.d 0 4) (by simp) with h289 | h289
                              · rcases p286_3 (m.d 1 4) (by simp) with h290 | h290
                                · rcases p286_3 (m.d 2 4) (by simp) with h291 | h291
                                  · linarith only [h274, h291, hlam]
                                  · rcases p286_3 (m.d 3 4) (by simp) with h293 | h293
                                    · linarith only [h276, h281, h282, h293, hlam]
                                    · rcases p286_3 (m.d 4 5) (by simp) with h295 | h295
                                      · linarith only [h276, h295, hlam]
                                      · linarith only [h282, h295, hlam]
                                · linarith only [h277, h290, hlam]
                              · linarith only [h274, h289, hlam]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              rcases p286_3 (m.d 0 4) (by simp) with h300 | h300
                              · rcases p286_3 (m.d 1 4) (by simp) with h301 | h301
                                · rcases p286_3 (m.d 2 4) (by simp) with h302 | h302
                                  · linarith only [h274, h302, hlam]
                                  · linarith only [h281, h302, hlam]
                                · linarith only [h279, h301, hlam]
                              · linarith only [h300, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h268, h277, h281, h282, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1, u1elo1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h268, h277, hc01, hlam, hphi, p286_1, u1elo1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              rcases p286_3 (m.d 0 4) (by simp) with h310 | h310
                              · linarith only [h268, h310, hlam]
                              · linarith only [h274, h310, hlam]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              rcases p286_3 (m.d 0 4) (by simp) with h313 | h313
                              · linarith only [h268, h313, hlam]
                              · linarith only [h276, h281, h282, h313, hlam]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h277, h281, h282, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1, u1elo1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h274, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h277, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h276, h282, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p286_1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h282, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h276, h281, h282, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p286_1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h279, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h281, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h284, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h276, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h280, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hc24, hlam, hphi, ht45, p286_1, u5elo4]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h268, h276, h277, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1, u1elo1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
                        · linarith only [h0, h274, h332, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                          · linarith only [h279, h332, h334, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h281, h334, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h268, h276, h280, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                      · linarith only [h0, h268, h274, h276, h279, h339, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                        · linarith only [h0, h274, h341, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                          · rcases h4bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h268, hlam, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              rcases p344_3 (m.d 0 4) (by simp) with h347 | h347
                              · rcases p344_3 (m.d 1 4) (by simp) with h348 | h348
                                · rcases p344_3 (m.d 2 4) (by simp) with h349 | h349
                                  · linarith only [h274, h349, hlam]
                                  · rcases p344_3 (m.d 3 4) (by simp) with h351 | h351
                                    · rcases p344_3 (m.d 4 5) (by simp) with h352 | h352
                                      · linarith only [h276, h352, hlam]
                                      · linarith only [h341, h352, hlam]
                                    · linarith only [h339, h351, hlam]
                                · linarith only [h277, h348, hlam]
                              · linarith only [h274, h347, hlam]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h268, h279, hlam, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h268, h339, h341, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo3]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h268, hc01, hlam, hphi, p344_1, u1elo3]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              rcases p344_3 (m.d 0 4) (by simp) with h362 | h362
                              · linarith only [h268, h362, hlam]
                              · linarith only [h274, h362, hlam]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h279, hlam, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h277, h339, h341, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h274, hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h277, hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h339, hlam, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h341, hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h276, h339, h341, hc23, hc34, hlam, hphi, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h268, hc01, hc34, hlam, hphi, ht12, ht23, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              rcases p344_3 (m.d 0 4) (by simp) with h374 | h374
                              · linarith only [h268, h279, h374, hlam]
                              · linarith only [h274, h374, hlam]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h339, h341, hc23, hc34, hlam, hphi, p344_1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h276, hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h338, hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h0, h274, h276, h339, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo1]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [h343, hlam, p344_0]
                            · have p344_0 := h344c.1
                              have p344_1 := h344c.2.1
                              have p344_2 := h344c.2.2.1
                              have p344_3 := h344c.2.2.2
                              linarith only [hlam, p344_0]
                          · linarith only [h0, h274, h276, h279, h343, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h268, h276, h338, hlam]
                · linarith only [h0, h274, h276, h278, hlam, hphi, u5ehi9, u5elo2]
              · linarith only [h0, h274, h277, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
              · rcases m.htr 1 2 5 (by decide) (by decide) with h389 | h389
                · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h391 | h391
                    · linarith only [h268, h276, h391, hc01, hlam, hphi, u1elo3]
                    · linarith only [h268, h391, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h394 | h394
                    · linarith only [h268, h276, h394, hc01, hlam, hphi, u1elo3]
                    · linarith only [h268, h394, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h389, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h268, h274, h275, h388, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi7]
          · linarith only [h274, h275, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h400 | h400
          · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
            · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
              · linarith only [h274, h400, h402, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                          · linarith only [h405, h409, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
                          · rcases h4bigk with h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h268, hlam, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h274, hlam, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h415 | h415
                              · rcases p411_3 (m.d 1 4) (by simp) with h416 | h416
                                · rcases p411_3 (m.d 2 4) (by simp) with h417 | h417
                                  · rcases p411_3 (m.d 3 4) (by simp) with h418 | h418
                                    · linarith only [h418, hlam, p411_0]
                                    · rcases p411_3 (m.d 4 5) (by simp) with h420 | h420
                                      · linarith only [h401, h420, hlam]
                                      · linarith only [h409, h420, hlam]
                                  · linarith only [h407, h417, hlam]
                                · linarith only [h405, h416, hlam]
                              · linarith only [h415, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h268, h405, h409, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p411_1, u1elo2]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h268, h405, hc01, hlam, hphi, p411_1, u1elo2]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h402, hlam, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h430 | h430
                              · linarith only [h268, h430, hlam]
                              · linarith only [h274, h400, h408, h409, h430, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h405, h409, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p411_1, u1elo2]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h274, h400, h407, h408, h409, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h268, h407, hc01, hc23, hlam, hphi, ht12, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h274, h400, h408, h409, hlam, p411_2]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h438 | h438
                              · linarith only [h274, h438, hlam]
                              · linarith only [h401, h438, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h274, h400, h408, h409, hlam, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h405, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h407, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h409, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h401, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h406, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h408, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h0, h400, h408, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p411_1, u1elo1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                        · linarith only [h268, h274, h401, h405, h408, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · linarith only [h0, h400, h402, h405, h407, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi7]
                    · linarith only [h268, h401, h406, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                          · rcases h4bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, hlam, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h274, hlam, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, h405, hlam, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, h405, h455, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, h405, h455, hc01, hc23, hlam, hphi, ht12, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h402, hlam, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h405, hlam, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h405, h455, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h274, h400, h456, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, hc01, hc24, hlam, hphi, ht12, p458_1]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, h274, h400, h405, h455, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              rcases p458_3 (m.d 0 4) (by simp) with h473 | h473
                              · linarith only [h274, h473, hlam]
                              · linarith only [h401, h473, hlam]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h274, h400, h456, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h268, h274, h400, h456, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h455, hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h455, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi9]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h401, hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h454, hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h456, hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [h457, hlam, p458_0]
                            · have p458_0 := h458c.1
                              have p458_1 := h458c.2.1
                              have p458_2 := h458c.2.2.1
                              have p458_3 := h458c.2.2.2
                              linarith only [hlam, p458_0]
                          · linarith only [h0, h400, h405, h456, h457, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h268, h274, h401, h405, h455, h456, hc02, hc23, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h488 | h488
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                          · rcases h4bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h268, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h274, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h0, h400, h402, h455, h488, hc04, hlam, hphi, ht0b, ht5b, p490_1, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h268, hlam, hphi, ht01, ht0b, ht5b, p490_1, u1elo3, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h268, hc01, hlam, hphi, p490_1, u1elo3]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h402, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h405, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p490_1, u1elo3, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h274, h400, h455, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p490_1, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h268, h455, hc01, hc34, hlam, hphi, ht12, ht23, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h455, hlam, p490_1]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              rcases p490_3 (m.d 0 4) (by simp) with h505 | h505
                              · linarith only [h274, h505, hlam]
                              · linarith only [h401, h505, hlam]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h274, h400, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p490_1, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h268, h274, h400, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p490_1, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h274, h400, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p490_1, u5ehi9]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              rcases p490_3 (m.d 0 4) (by simp) with h512 | h512
                              · linarith only [h268, h405, h512, hlam]
                              · linarith only [h401, h512, hlam]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h401, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h454, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h488, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [h489, hlam, p490_0]
                            · have p490_0 := h490c.1
                              have p490_1 := h490c.2.1
                              have p490_2 := h490c.2.2.1
                              have p490_3 := h490c.2.2.2
                              linarith only [hlam, p490_0]
                          · linarith only [h0, h400, h402, h455, h488, h489, hlam]
                        · linarith only [h0, h400, h402, h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                    · linarith only [h268, h401, h454, hlam]
                · linarith only [h0, h400, h404, hlam]
            · linarith only [h274, h400, h401, hlam, hphi, u5ehi7, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
            · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
              · linarith only [h274, h525, h526, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h528 | h528
                · linarith only [h400, h526, h528, hc02, hc24, hlam, hphi]
                · linarith only [h0, h528, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
              · linarith only [h0, h274, h531, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
                · linarith only [h0, h400, h531, h533, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h533, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_20_11_13_14_M_LI_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h4, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h13, h4, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h4, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h15, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h18, h20, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h20, h5, h8, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h24, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h23, h24, h26, h4, h7, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h24, h28, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                          · linarith only [h1, h30, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h30, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h33, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                      · linarith only [h0, h33, h35, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h23, h35, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
                · linarith only [h38, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h4, h40, h6, hlam, hphi, ht34, u3ehi2, u4elo0]
                  · linarith only [h4, h40, h6, hlam, hphi, ht34, u3ehi2, u4elo4]
            · linarith only [h4, h5, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h44 | h44
            · rcases m.htr 0 2 5 (by decide) (by decide) with h45 | h45
              · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                    · linarith only [h4, h44, h48, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                          · linarith only [h1, h52, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h52, hlam, hphi, ht34, u3ehi1, u4elo3]
                        · linarith only [h4, h45, h51, hc12, hc23, hlam, hphi]
                      · linarith only [h4, h44, h50, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · linarith only [h4, h45, h57, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                          · linarith only [h1, h61, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h61, hlam, hphi, ht34, u3ehi1, u4elo3]
                        · linarith only [h4, h45, h60, hc12, hc23, hlam, hphi]
                      · linarith only [h4, h44, h59, hc12, hc23, hlam, hphi]
                · linarith only [h4, h45, h46, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h67 | h67
                · rcases m.htr 0 4 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h44, h45, h68, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h70, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h0, h45, h73, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                          · linarith only [h1, h75, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h75, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · linarith only [h44, h45, h72, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h4, h44, h67, h79, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                    · linarith only [h4, h44, h81, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                        · linarith only [h0, h45, h84, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                          · linarith only [h1, h86, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h86, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · linarith only [h44, h45, h83, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
                · linarith only [h44, h90, h91, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h44, h90, h91, hlam, hphi, ht34, u3ehi0, u4elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h94 | h94
                · rcases m.htr 0 4 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
                    · linarith only [h0, h96, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h44, h98, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                        · linarith only [h0, h100, h90, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                          · linarith only [h1, h102, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h102, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                    · linarith only [h0, h105, h4, h44, h94, h95, hlam, hphi, ht34, u3ehi4, u4elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                      · linarith only [h0, h107, h44, h95, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h109, h90, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                          · linarith only [h1, h111, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                          · linarith only [h111, hlam, hphi, ht34, u3ehi1, u4elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                    · linarith only [h0, h115, h44, hlam, hphi, ht34, u3ehi2, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                      · linarith only [h0, h117, h44, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h0, h119, h90, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                          · linarith only [h1, h114, h121, h94, hlam, hphi, ht34, u3ehi3, u4elo0]
                          · linarith only [h121, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h124, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h0, h126, h44, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                        · linarith only [h0, h128, h90, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                          · linarith only [h1, h130, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h130, hlam, hphi, ht34, u3ehi1, u4elo3]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h135 | h135
      · rcases m.htr 0 1 5 (by decide) (by decide) with h136 | h136
        · rcases m.htr 0 2 3 (by decide) (by decide) with h137 | h137
          · linarith only [h0, h1, h137, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 0 2 5 (by decide) (by decide) with h140 | h140
              · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
                · rcases m.htr 0 4 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                    · linarith only [h0, h1, h137, h143, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                      · linarith only [h0, h1, h145, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h139, h145, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                    · linarith only [h0, h1, h148, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
                      · linarith only [h0, h1, h150, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h139, h150, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h1, h136, h141, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
                · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                  · linarith only [h139, h140, h155, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
                    · linarith only [h0, h1, h157, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                      · linarith only [h0, h1, h159, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h1, h136, h139, h140, h159, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h1, h136, h154, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h163 | h163
              · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                · linarith only [h139, h163, h164, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h139, h163, h164, hlam, hphi, ht34, u3ehi0, u4elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
                · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                    · linarith only [h0, h1, h169, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                      · linarith only [h0, h1, h139, h171, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                        · linarith only [h0, h163, h173, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                          · linarith only [h1, h135, h175, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                          · linarith only [h1, h175, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                    · linarith only [h0, h137, h167, h178, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                      · linarith only [h0, h1, h180, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                        · linarith only [h1, h135, h163, h180, h182, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                          · linarith only [h1, h135, h184, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                          · linarith only [h1, h184, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1, h136, h167, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h188 | h188
          · linarith only [h0, h1, h188, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h190 | h190
            · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
              · linarith only [h0, h136, h191, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                  · linarith only [h0, h136, h190, h194, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
                    · linarith only [h188, h190, h196, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h198 | h198
                      · linarith only [h0, h1, h198, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h190, h191, h198, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
                  · linarith only [h1, h135, h193, h201, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                    · linarith only [h188, h190, h203, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                      · linarith only [h0, h1, h205, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h190, h191, h205, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h208 | h208
              · linarith only [h0, h136, h190, h208, hc12, hlam, hphi, ht23, ht34, u4elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h210 | h210
                · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                  · linarith only [h135, h136, h211, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                    · linarith only [h0, h213, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                      · linarith only [h0, h136, h215, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                        · linarith only [h135, h136, h208, h215, h217, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                          · linarith only [h135, h136, h219, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi3]
                          · linarith only [h1, h219, hlam, hphi, ht34, u3ehi0, u4elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h222 | h222
                  · linarith only [h1, h135, h210, h222, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                    · linarith only [h0, h136, h224, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                      · linarith only [h0, h136, h226, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                        · linarith only [h135, h136, h226, h228, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                          · linarith only [h135, h136, h230, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi3]
                          · linarith only [h1, h135, h226, h230, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h0, h135, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h234 | h234
    · linarith only [h0, h234, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h236 | h236
      · rcases m.htr 0 1 5 (by decide) (by decide) with h237 | h237
        · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
          · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
            · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
              · rcases m.htr 0 3 5 (by decide) (by decide) with h241 | h241
                · rcases m.htr 0 4 5 (by decide) (by decide) with h242 | h242
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                          · linarith only [h234, h236, h243, h246, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h234, h236, h244, h246, hc24, hlam, hphi, u4elo3]
                        · linarith only [h0, h236, h240, h241, h242, h245, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                      · linarith only [h0, h236, h241, h242, h244, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h0, h238, h243, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                          · linarith only [h234, h236, h252, h255, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h234, h255, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h234, h237, h240, h241, h252, h254, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                      · linarith only [h234, h237, h241, h252, h253, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h0, h238, h252, hlam]
                · linarith only [h234, h237, h241, hlam]
              · linarith only [h0, h237, h240, hlam]
            · linarith only [h238, h239, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
              · rcases m.htr 0 3 5 (by decide) (by decide) with h266 | h266
                · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                    · linarith only [h238, h264, h268, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                          · linarith only [h0, h236, h272, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h0, h268, h272, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h236, h265, h266, h267, h271, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                      · linarith only [h0, h236, h266, h267, h270, hlam, hphi, ht34, u3ehi4, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                    · linarith only [h0, h238, h277, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                          · linarith only [h0, h236, h277, h281, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h277, h281, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h237, h265, h266, h280, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                      · linarith only [h0, h237, h266, h279, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h0, h237, h238, h266, hlam]
              · linarith only [h0, h237, h265, hlam]
            · linarith only [h0, h236, h264, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
          · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
            · rcases m.htr 0 2 5 (by decide) (by decide) with h291 | h291
              · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
                · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
                  · linarith only [h236, h237, h293, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h297 | h297
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                          · linarith only [h234, h236, h295, h298, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h234, h298, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h289, h291, h292, h297, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi4]
                      · linarith only [h0, h289, h292, h296, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h0, h289, h295, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
                  · linarith only [h236, h237, h304, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h308 | h308
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
                          · linarith only [h234, h236, h309, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                          · linarith only [h309, hlam, hphi, ht34, u3ehi1, u4elo3]
                        · linarith only [h0, h291, h308, hlam]
                      · linarith only [h0, h307, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h289, h306, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
                · linarith only [h289, h291, h315, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                  · linarith only [h0, h236, h291, h317, hlam]
                  · linarith only [h289, h291, h317, hlam, hphi, ht34, u3ehi2, u4elo4]
            · linarith only [h289, h290, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h321 | h321
            · rcases m.htr 0 2 5 (by decide) (by decide) with h322 | h322
              · rcases m.htr 0 3 5 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                  · linarith only [h236, h237, h324, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                    · linarith only [h289, h322, h323, h326, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                          · linarith only [h236, h237, h329, h330, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                          · linarith only [h237, h326, h329, h330, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h322, h329, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h236, h328, hc14, hlam, hphi, u4elo2]
                · linarith only [h289, h322, h323, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h336 | h336
                · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
                  · linarith only [h236, h237, h337, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                    · linarith only [h289, h321, h339, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                        · linarith only [h0, h236, h322, h341, h342, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                          · linarith only [h0, h236, h339, h344, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h339, h344, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h236, h341, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
                  · linarith only [h234, h236, h336, h348, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                    · linarith only [h0, h289, h350, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                        · linarith only [h0, h236, h322, h350, h352, h353, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                          · linarith only [h0, h236, h350, h355, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h350, h355, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h236, h352, hc14, hlam, hphi, u4elo2]
            · linarith only [h0, h236, h321, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h360 | h360
        · rcases m.htr 0 2 3 (by decide) (by decide) with h361 | h361
          · rcases m.htr 0 2 4 (by decide) (by decide) with h362 | h362
            · rcases m.htr 0 2 5 (by decide) (by decide) with h363 | h363
              · rcases m.htr 0 3 5 (by decide) (by decide) with h364 | h364
                · linarith only [h236, h360, h364, hlam, hphi, ht34, u3ehi4, u4elo1]
                · linarith only [h236, h360, h364, hlam, hphi, ht34, u3ehi0, u4elo1]
              · linarith only [h0, h360, h363, hlam]
            · linarith only [h361, h362, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h369 | h369
            · rcases m.htr 0 2 5 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 3 5 (by decide) (by decide) with h371 | h371
                · linarith only [h236, h360, h371, hlam, hphi, ht34, u3ehi4, u4elo1]
                · linarith only [h236, h360, h371, hlam, hphi, ht34, u3ehi0, u4elo1]
              · linarith only [h236, h360, h369, h370, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h375 | h375
              · rcases m.htr 0 3 5 (by decide) (by decide) with h376 | h376
                · linarith only [h0, h360, h369, h376, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h0, h360, h369, h376, hlam, hphi, ht34, u3ehi0, u4elo2]
              · linarith only [h0, h360, h375, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h380 | h380
          · rcases m.htr 0 2 4 (by decide) (by decide) with h381 | h381
            · rcases m.htr 0 2 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
                · rcases m.htr 0 4 5 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h389 | h389
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h390 | h390
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                                · linarith only [h0, h380, h391, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                                · linarith only [h391, hlam, hphi, ht34, u3ehi2, u4elo3]
                              · linarith only [h384, h390, hc14, hlam, hphi, u4elo0]
                            · linarith only [h234, h383, h389, hlam]
                          · linarith only [h234, h383, h388, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h360, h382, h387, hc01, hlam, hphi, u1elo4]
                      · linarith only [h0, h381, h386, hlam]
                    · linarith only [h0, h380, h385, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                              · linarith only [h384, h405, hc04, hlam, hphi, u4elo1]
                              · linarith only [h236, h405, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                            · linarith only [h234, h383, h404, hlam]
                          · linarith only [h234, h383, h403, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h382, h402, hlam]
                      · linarith only [h0, h380, h383, h401, hlam, hphi, ht34, u3ehi4, u4elo2]
                    · linarith only [h0, h380, h400, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h415 | h415
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                            · linarith only [h383, h418, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · linarith only [h417, h418, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h417, hlam, hphi, ht34, u3ehi1, u4elo3]
                        · linarith only [h0, h382, h416, hlam]
                      · linarith only [h0, h381, h415, hlam]
                    · linarith only [h0, h234, h380, h414, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h428 | h428
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
                            · linarith only [h383, h425, h429, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi0]
                            · linarith only [h428, h429, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h428, hlam, hphi, ht34, u3ehi1, u4elo3]
                        · linarith only [h0, h382, h427, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h426, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h380, h425, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
                · linarith only [h380, h382, h436, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
                  · linarith only [h236, h380, h382, h438, hlam, hphi, ht34, u3ehi2, u4elo1]
                  · linarith only [h380, h382, h438, hlam, hphi, ht34, u3ehi2, u4elo4]
            · linarith only [h380, h381, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h442 | h442
            · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
              · rcases m.htr 0 3 5 (by decide) (by decide) with h444 | h444
                · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                    · linarith only [h380, h442, h446, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h451 | h451
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h452 | h452
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                                    · rcases h0bigk with h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c
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
                                        linarith only [h234, hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h236, hlam, p456_1]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h360, hlam, p456_1]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h0, h446, hc01, hc23, hlam, hphi, ht12, p456_1]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h380, hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h0, h443, h445, h446, h454, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p456_1, u3ehi4]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h0, h443, h446, h454, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p456_1, u3ehi4]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h234, hc01, hlam, hphi, p456_1, u1elo2]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h0, h234, hc01, hlam, hphi, p456_1, u1elo2]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h234, h443, h445, h454, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u1elo2, u3ehi4]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h234, h443, h454, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u1elo2, u3ehi4]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p456_1, u4elo0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h442, hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p456_1, u0elo3, u3ehi0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h236, h443, h454, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u1elo3, u3ehi4]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h360, hc01, hlam, hphi, p456_1, u1elo4]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h443, hlam, p456_1]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h444, hlam, p456_0]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [h445, hlam, p456_1]
                                      · have p456_0 := h456c.1
                                        have p456_1 := h456c.2.1
                                        have p456_2 := h456c.2.2.1
                                        have p456_3 := h456c.2.2.2
                                        linarith only [hlam, p456_0]
                                    · linarith only [h455, hlam, hphi, ht34, u3ehi3, u4elo4]
                                  · linarith only [h0, h442, h446, h453, h454, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h0, h446, h453, hc02, hlam, hphi, ht23, ht34, u4elo3]
                              · linarith only [h236, h445, h452, hlam]
                            · linarith only [h444, h451, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h234, h444, h450, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h443, h449, hlam]
                      · linarith only [h0, h448, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                    · linarith only [h380, h443, h444, h490, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                              · linarith only [h445, h496, hc04, hlam, hphi, u4elo1]
                              · linarith only [h236, h496, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                            · linarith only [h0, h443, h444, h490, h494, h495, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h234, h444, h494, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h443, h493, hlam]
                      · linarith only [h0, h442, h492, hlam]
                · linarith only [h380, h443, h444, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h504 | h504
                · rcases m.htr 0 4 5 (by decide) (by decide) with h505 | h505
                  · linarith only [h442, h443, h505, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                    · linarith only [h380, h442, h507, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h509 | h509
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h510 | h510
                        · linarith only [h442, h443, h507, h510, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                              · linarith only [h505, h514, hc04, hlam, hphi, u4elo1]
                              · linarith only [h236, h514, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                            · linarith only [h504, h513, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h234, h504, h512, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h0, h442, h509, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h520 | h520
                  · linarith only [h380, h442, h504, h520, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
                    · linarith only [h380, h442, h522, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h525 | h525
                        · linarith only [h442, h443, h525, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                            · linarith only [h504, h528, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · linarith only [h527, h528, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h527, hlam, hphi, ht34, u3ehi1, u4elo3]
                      · linarith only [h0, h442, h524, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h533 | h533
              · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
                · linarith only [h442, h533, h534, hlam, hphi, ht34, u3ehi4, u4elo2]
                · linarith only [h442, h533, h534, hlam, hphi, ht34, u3ehi0, u4elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h537 | h537
                · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
                    · linarith only [h0, h380, h539, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h541 | h541
                      · linarith only [h0, h442, h541, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h541, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                    · linarith only [h0, h380, h544, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                      · linarith only [h0, h442, h546, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h546, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h549 | h549
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                    · linarith only [h0, h380, h550, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h552 | h552
                      · linarith only [h0, h442, h550, h552, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h552, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h555 | h555
                    · linarith only [h0, h380, h555, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
                      · linarith only [h0, h442, h555, h557, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h557, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

end R2N4
