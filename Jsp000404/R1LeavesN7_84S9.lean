import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_14_H_L_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h12, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · linarith only [h12, h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · linarith only [h11, h2, h5, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h10, h2, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · linarith only [h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h7, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h1, h24, h6, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                          · linarith only [h2, h26, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · linarith only [h0, h2, h23, h26, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h2, h23, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h20, h22, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h20, h21, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h20, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                      · linarith only [h0, h37, h5, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                          · linarith only [h2, h40, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                            · linarith only [h3, h42, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h3, h33, h40, h42, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · linarith only [h3, h33, h39, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · linarith only [h34, h36, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h34, h35, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h34, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                      · linarith only [h0, h5, h52, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                        · linarith only [h1, h33, h54, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                          · linarith only [h0, h49, h5, h56, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                            · linarith only [h3, h58, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                              · rcases h4bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h33, h51, h56, h58, h60, hc14, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p61_1, u2elo1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h33, h56, h60, hc23, hc34, hlam, hphi, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h5, hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h33, hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h1, hlam, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h1, h33, h56, h60, hc23, hc34, hlam, hphi, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h52, hlam, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h54, hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h3, hlam, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h50, hlam, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h56, hlam, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h58, hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  rcases p61_3 (m.d 0 4) (by simp) with h77 | h77
                                  · linarith only [h5, h77, hlam]
                                  · rcases p61_3 (m.d 1 4) (by simp) with h79 | h79
                                    · linarith only [h52, h79, hlam]
                                    · rcases p61_3 (m.d 2 4) (by simp) with h81 | h81
                                      · linarith only [h56, h81, hlam]
                                      · rcases p61_3 (m.d 3 4) (by simp) with h83 | h83
                                        · rcases p61_3 (m.d 4 5) (by simp) with h84 | h84
                                          · linarith only [h60, h84, hlam]
                                          · linarith only [h33, h84, hlam]
                                        · linarith only [h5, h83, hlam]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  rcases p61_3 (m.d 0 4) (by simp) with h88 | h88
                                  · linarith only [h5, h88, hlam]
                                  · linarith only [h1, h88, hlam]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  rcases p61_3 (m.d 0 4) (by simp) with h91 | h91
                                  · linarith only [h5, h91, hlam]
                                  · linarith only [h3, h91, hlam]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h3, h33, h56, hc23, hc34, hlam, hphi, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h0, h49, h5, h60, hc23, hc34, hlam, hphi, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h50, h56, h60, hc23, hc34, hlam, hphi, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h56, h60, hc23, hc34, hlam, hphi, p61_1]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [h60, hlam, p61_0]
                                · have p61_0 := h61c.1
                                  have p61_1 := h61c.2.1
                                  have p61_2 := h61c.2.2.1
                                  have p61_3 := h61c.2.2.2
                                  linarith only [hlam, p61_0]
                              · rcases h4bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h3, h50, h56, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p101_1, u2elo0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h3, h56, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p101_1, u2elo0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h5, hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h33, hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h1, hlam, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h1, h3, h56, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p101_1, u2elo0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h52, hlam, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h54, hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h3, hlam, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h50, hlam, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h56, hlam, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h58, hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h60, hc04, hc45, hlam, hphi, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h50, h56, h60, hc23, hc45, hlam, hphi, ht34, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h56, h60, hc23, hc45, hlam, hphi, ht34, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h60, hlam, p101_0]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  rcases p101_3 (m.d 0 4) (by simp) with h122 | h122
                                  · linarith only [h122, hlam, p101_0]
                                  · rcases p101_3 (m.d 1 4) (by simp) with h124 | h124
                                    · linarith only [h124, h54, hlam]
                                    · rcases p101_3 (m.d 2 4) (by simp) with h126 | h126
                                      · linarith only [h126, h58, hlam]
                                      · rcases p101_3 (m.d 3 4) (by simp) with h128 | h128
                                        · linarith only [h128, h60, hlam]
                                        · linarith only [h128, h5, hlam]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  rcases p101_3 (m.d 0 4) (by simp) with h131 | h131
                                  · linarith only [h131, h33, hlam]
                                  · linarith only [h1, h131, hlam]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  rcases p101_3 (m.d 0 4) (by simp) with h134 | h134
                                  · linarith only [h134, h33, hlam]
                                  · linarith only [h134, h3, hlam]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [h0, h49, h5, hc23, hc45, hlam, hphi, ht34, p101_1]
                                · have p101_0 := h101c.1
                                  have p101_1 := h101c.2.1
                                  have p101_2 := h101c.2.2.1
                                  have p101_3 := h101c.2.2.2
                                  linarith only [hlam, p101_0]
                    · linarith only [h51, hc12, hlam, hphi, u2elo4]
                  · linarith only [h49, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h49, hc12, hlam, hphi, u2elo2]
          · linarith only [h4, hc02, hlam, hphi, u2elo4]
        · linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
      · linarith only [h2, hc02, hlam, hphi, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h145 | h145
      · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
        · rcases m.htr 0 2 5 (by decide) (by decide) with h147 | h147
          · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
            · linarith only [h0, h1, h148, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
              · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
                  · linarith only [h1, h152, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h152, hc12, hlam, hphi, u2elo3]
                · linarith only [h151, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                  · linarith only [h1, h157, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h157, hc12, hlam, hphi, u2elo3]
                · linarith only [h156, hc12, hlam, hphi, u2elo2]
          · linarith only [h147, hc02, hlam, hphi, u2elo4]
        · linarith only [h145, h146, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
      · linarith only [h145, hc02, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h164 | h164
    · rcases m.htr 0 2 3 (by decide) (by decide) with h165 | h165
      · rcases m.htr 0 2 4 (by decide) (by decide) with h166 | h166
        · rcases m.htr 0 2 5 (by decide) (by decide) with h167 | h167
          · rcases m.htr 0 3 4 (by decide) (by decide) with h168 | h168
            · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
              · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                · linarith only [h0, h170, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h170, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                · linarith only [h0, h164, h173, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h173, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h164, h168, hlam]
          · linarith only [h0, h164, h165, h167, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
        · linarith only [h0, h164, h165, h166, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
      · linarith only [h165, hc02, hlam, hphi, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h180 | h180
      · rcases m.htr 0 2 4 (by decide) (by decide) with h181 | h181
        · rcases m.htr 0 2 5 (by decide) (by decide) with h182 | h182
          · rcases m.htr 0 3 4 (by decide) (by decide) with h183 | h183
            · rcases m.htr 0 4 5 (by decide) (by decide) with h184 | h184
              · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                · linarith only [h0, h185, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h185, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                · linarith only [h0, h188, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h188, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                · linarith only [h0, h192, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h180, h192, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · linarith only [h0, h195, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h180, h195, hc12, hlam, hphi, u2elo0]
          · linarith only [h182, hc02, hlam, hphi, u2elo4]
        · linarith only [h180, h181, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
      · linarith only [h180, hc02, hlam, hphi, u2elo2]

end R2N4
