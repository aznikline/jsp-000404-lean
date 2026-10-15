import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_0_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h1, h10, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h10, h12, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h14, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                          · linarith only [h14, h2, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                    · linarith only [h2, h5, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                  · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h2, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h24, h5, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h1, h26, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h22, h24, h26, h28, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                          · linarith only [h2, h30, h5, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                            · linarith only [h1, h24, h32, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                            · rcases h5bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p34_1, u1elo0, u5ehi1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h3, h30, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p34_1, u2elo0, u4ehi2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h1, h26, h32, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p34_1, u2elo0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h5, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h30, hlam, hphi, ht01, ht0b, ht45, ht5b, p34_1, u1elo4, u4ehi2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, h26, h32, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34_1, u1elo0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h24, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h3, hlam, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h23, hlam, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h28, hlam, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h30, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h4, hlam, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p34_1, u2elo0, u5ehi1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h1, h30, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p34_1, u2elo0, u4ehi2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h32, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, h23, h30, hc45, hlam, hphi, p34_1, u4ehi2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h23, h30, hc45, hlam, hphi, p34_1, u4ehi2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h30, hc45, hlam, hphi, p34_1, u4ehi2]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h28, hc23, hc45, hlam, hphi, ht34, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                  · linarith only [h23, h3, hc12, hlam, hphi, u2elo0]
                · linarith only [h2, h21, h22, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1, h21, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
              · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                      · linarith only [h1, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                        · linarith only [h2, h4, h68, h70, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h2, h72, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · linarith only [h67, h72, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                    · linarith only [h2, h63, h67, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                  · linarith only [h3, h66, hc12, hlam, hphi, u2elo0]
                · linarith only [h2, h64, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1, h64, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
              · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                    · linarith only [h63, h82, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h79, h84, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                        · linarith only [h0, h4, h80, h82, h84, h86, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                          · linarith only [h0, h80, h82, h88, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                            · rcases h5bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h3, h82, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p91_1, u2elo0, u4ehi1]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h3, h88, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p91_1, u2elo0, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h4, hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h63, hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h0, hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h88, hlam, hphi, ht01, ht0b, ht45, ht5b, p91_1, u1elo4, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h0, h2, h63, h90, hlam, hphi, ht01, ht0b, ht45, ht5b, p91_1, u1elo0, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h82, hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h3, hlam, p91_1]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h81, hlam, p91_1]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h86, hlam, p91_1]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h88, hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                rcases p91_3 (m.d 0 5) (by simp) with h107 | h107
                                · linarith only [h107, h4, hlam]
                                · rcases p91_3 (m.d 1 5) (by simp) with h109 | h109
                                  · linarith only [h0, h109, hlam, p91_1]
                                  · rcases p91_3 (m.d 2 5) (by simp) with h111 | h111
                                    · linarith only [h111, h86, hlam]
                                    · rcases p91_3 (m.d 3 5) (by simp) with h113 | h113
                                      · rcases p91_3 (m.d 4 5) (by simp) with h114 | h114
                                        · linarith only [h114, h90, hlam]
                                        · linarith only [h114, h63, hlam]
                                      · linarith only [h113, h4, hlam]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                rcases p91_3 (m.d 0 5) (by simp) with h118 | h118
                                · linarith only [h118, h4, hlam]
                                · linarith only [h0, h118, hlam]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                rcases p91_3 (m.d 0 5) (by simp) with h121 | h121
                                · linarith only [h121, h4, hlam]
                                · linarith only [h121, h3, hlam]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [hlam, p91_0]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h2, h63, h90, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p91_1, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h3, h88, hc45, hlam, hphi, p91_1, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h81, h88, hc45, hlam, hphi, p91_1, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h88, hc45, hlam, hphi, p91_1, u4ehi2]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [h90, hlam, p91_1]
                              · have p91_0 := h91c.1
                                have p91_1 := h91c.2.1
                                have p91_2 := h91c.2.2.1
                                have p91_3 := h91c.2.2.2
                                linarith only [hlam, p91_0]
                            · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h0, h81, h88, hlam, hphi, ht01, ht0b, ht45, ht5b, p131_1, u1elo0, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h3, h88, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p131_1, u2elo0, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h4, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h63, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h0, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h88, hlam, hphi, ht01, ht0b, ht45, ht5b, p131_1, u1elo4, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p131_1, u1elo0, u5ehi3]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h82, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h3, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h81, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h86, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h88, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h3, h88, h90, hc45, hlam, hphi, p131_1, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h81, h88, h90, hc45, hlam, hphi, p131_1, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h88, h90, hc45, hlam, hphi, p131_1, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h90, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h0, h81, h88, hc45, hlam, hphi, p131_1, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h81, h88, hc45, hlam, hphi, p131_1, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h88, hc45, hlam, hphi, p131_1, u4ehi2]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h4, hc03, hc45, hlam, hphi, ht34, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                  · linarith only [h3, h81, hc12, hlam, hphi, u2elo0]
                · linarith only [h2, h79, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1, h79, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
        · linarith only [h161, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
          · linarith only [h1, h163, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
            · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
              · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                · linarith only [h167, h2, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                  · linarith only [h1, h161, h167, h169, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                      · linarith only [h1, h172, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                        · linarith only [h1, h174, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                            · rcases h5bigk with h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p178_1, u1elo0, u5ehi1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h161, hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h163, hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h161, h176, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p178_1, u2elo3, u4ehi4]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h0, hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h169, hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h161, h174, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p178_1, u1elo4]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p178_1, u1elo0, u4ehi4]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p178_1, u2elo4, u5ehi0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p178_1, u2elo4, u5ehi1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h174, hlam, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h176, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p178_1, u2elo3, u4ehi4]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h0, h166, h169, hc23, hc35, hlam, hphi, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h166, h169, h177, hc23, hc34, hlam, hphi, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h1, h161, h177, hc23, hc34, hlam, hphi, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, p178_0]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                rcases p178_3 (m.d 0 5) (by simp) with h198 | h198
                                · linarith only [h163, h198, hlam]
                                · linarith only [h165, h198, hlam]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h165, hlam, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h171, hlam, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h176, hlam, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [h177, hlam, p178_1]
                              · have p178_0 := h178c.1
                                have p178_1 := h178c.2.1
                                have p178_2 := h178c.2.2.1
                                have p178_3 := h178c.2.2.2
                                linarith only [hlam, p178_0]
                            · linarith only [h171, h177, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                          · linarith only [h0, h171, h176, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi0]
                    · linarith only [h165, h171, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
              · linarith only [h1, h161, h166, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
              · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                · linarith only [h1, h2, h211, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                  · linarith only [h1, h161, h213, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h215 | h215
                    · linarith only [h165, h211, h215, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                      · linarith only [h1, h217, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h219 | h219
                        · linarith only [h0, h210, h211, h215, h219, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h221 | h221
                          · linarith only [h165, h2, h221, hc02, hlam, hphi, u2elo3]
                          · linarith only [h1, h2, h221, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1, h2, h210, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h225 | h225
      · linarith only [h1, h225, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
        · linarith only [h1, h227, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
          · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
            · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
              · linarith only [h1, h231, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                · linarith only [h225, h231, h233, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                  · linarith only [h227, h231, h235, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h239 | h239
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h240 | h240
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h241 | h241
                            · linarith only [h238, h241, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                            · linarith only [h225, h230, h238, h241, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                          · linarith only [h225, h230, h240, hlam]
                        · linarith only [h225, h229, h230, h238, h239, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                            · rcases h5bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h0, h237, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo0, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h227, hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h227, h238, h246, h248, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p249_1, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h227, h238, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p249_1, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h0, hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h235, hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h248, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo4, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo0, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h238, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p249_1, u5ehi0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h238, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p249_1, u5ehi1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h238, h246, h248, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p249_1, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h238, h246, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p249_1, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h229, hlam, p249_1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h1, h229, h235, h238, hc12, hc34, hlam, hphi, ht23, p249_1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h246, hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [hlam, p249_0]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h0, h229, hlam, hphi, ht01, ht0b, ht45, ht5b, p249_1, u1elo0, u4ehi4]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h230, hlam, p249_1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h237, hlam, p249_1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h247, hlam, p249_1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [h248, hlam, p249_1]
                              · have p249_0 := h249c.1
                                have p249_1 := h249c.2.1
                                have p249_2 := h249c.2.2.1
                                have p249_3 := h249c.2.2.2
                                linarith only [hlam, p249_0]
                            · linarith only [h1, h237, h238, h248, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h225, h230, h247, hlam]
                        · linarith only [h1, h229, h246, hlam]
                    · linarith only [h225, h230, h237, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
              · linarith only [h1, h229, h279, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h281 | h281
                · linarith only [h279, h281, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h283 | h283
                  · linarith only [h227, h279, h283, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
                    · linarith only [h230, h285, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h288 | h288
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h289 | h289
                          · linarith only [h281, h285, h287, h289, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h291 | h291
                            · linarith only [h287, h291, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                            · rcases h5bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p293_1, u1elo0, u5ehi1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h227, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h1, h229, h291, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u2elo2, u4ehi3]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h230, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h0, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h283, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h291, hlam, hphi, ht01, ht0b, ht45, ht5b, p293_1, u1elo4, u4ehi3]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h285, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h288, hlam, hphi, ht01, ht0b, ht12, ht5b, p293_1, u2elo2, u5ehi0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h288, hlam, hphi, ht01, ht0b, ht12, ht5b, p293_1, u2elo2, u5ehi1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h288, h291, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p293_1, u2elo2, u4ehi3]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h289, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h229, hlam, p293_1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h0, h229, h285, hlam, hphi, ht01, ht0b, ht45, ht5b, p293_1, u1elo0, u4ehi1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h288, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h291, hlam, p293_0]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h0, h285, hc45, hlam, hphi, p293_1, u4ehi1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h285, hc45, hlam, hphi, p293_1, u4ehi1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h227, hc02, hc45, hlam, hphi, ht23, ht34, p293_1]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [h291, hc45, hlam, hphi, p293_1, u4ehi3]
                              · have p293_0 := h293c.1
                                have p293_1 := h293c.2.1
                                have p293_2 := h293c.2.2.1
                                have p293_3 := h293c.2.2.2
                                linarith only [hlam, p293_0]
                        · linarith only [h1, h229, h288, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                          · linarith only [h230, h321, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · linarith only [h287, h320, h321, hlam]
                        · linarith only [h1, h229, h320, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
            · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
              · linarith only [h1, h326, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                · linarith only [h225, h326, h328, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                  · linarith only [h227, h326, h330, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
                        · linarith only [h1, h229, h334, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                          · linarith only [h333, h334, h336, hlam]
                          · linarith only [h332, h336, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                        · linarith only [h1, h229, h339, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                            · rcases h5bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h0, h332, hlam, hphi, ht01, ht0b, ht45, ht5b, p343_1, u1elo0, u4ehi4]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h227, hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h229, hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h227, h341, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p343_1, u2elo3, u4ehi4]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h0, hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h330, hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h326, h339, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p343_1, u1elo4]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p343_1, u1elo0, u4ehi4]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h341, hlam, hphi, ht01, ht0b, ht12, ht5b, p343_1, u2elo3, u5ehi0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h341, hlam, hphi, ht01, ht0b, ht12, ht5b, p343_1, u2elo3, u5ehi1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h339, hlam, p343_1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h341, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p343_1, u2elo3, u4ehi4]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                rcases p343_3 (m.d 0 5) (by simp) with h359 | h359
                                · linarith only [h229, h359, hlam]
                                · rcases p343_3 (m.d 1 5) (by simp) with h361 | h361
                                  · linarith only [h0, h361, hlam, p343_1]
                                  · rcases p343_3 (m.d 2 5) (by simp) with h363 | h363
                                    · linarith only [h339, h363, hlam]
                                    · linarith only [h227, h363, hlam]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                rcases p343_3 (m.d 0 5) (by simp) with h366 | h366
                                · linarith only [h229, h366, hlam]
                                · linarith only [h0, h366, hlam]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h227, h342, hc02, hc34, hlam, hphi, ht23, p343_1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [hlam, p343_0]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                rcases p343_3 (m.d 0 5) (by simp) with h371 | h371
                                · linarith only [h229, h371, hlam]
                                · linarith only [h325, h371, hlam]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h325, hlam, p343_1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h332, hlam, p343_1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h341, hlam, p343_1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [h342, hlam, p343_1]
                              · have p343_0 := h343c.1
                                have p343_1 := h343c.2.1
                                have p343_2 := h343c.2.2.1
                                have p343_3 := h343c.2.2.2
                                linarith only [hlam, p343_0]
                            · linarith only [h0, h332, h342, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                          · linarith only [h225, h325, h341, hlam]
                    · linarith only [h225, h325, h332, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
              · linarith only [h1, h382, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h384 | h384
                · linarith only [h382, h384, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h227, h325, h382, h386, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h388 | h388
                    · linarith only [h325, h388, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h390 | h390
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h391 | h391
                        · linarith only [h1, h229, h391, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
                          · linarith only [h388, h390, h391, h393, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h395 | h395
                            · linarith only [h390, h391, h393, h395, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h390, h391, h395, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                        · linarith only [h1, h229, h398, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h400 | h400
                          · linarith only [h325, h400, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                            · linarith only [h382, h390, h400, h402, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h382, h390, h402, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h405 | h405
    · rcases m.htr 0 2 4 (by decide) (by decide) with h406 | h406
      · rcases m.htr 0 2 5 (by decide) (by decide) with h407 | h407
        · rcases m.htr 0 3 5 (by decide) (by decide) with h408 | h408
          · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
            · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
              · rcases m.htr 1 2 4 (by decide) (by decide) with h411 | h411
                · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h413 | h413
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                      · linarith only [h405, h414, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                        · linarith only [h411, h414, h416, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h418 | h418
                          · linarith only [h411, h418, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h413, h418, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                    · linarith only [h406, h409, h413, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                  · linarith only [h407, h412, hc12, hlam, hphi, u2elo0]
                · linarith only [h406, h410, h411, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h405, h410, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
              · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
                · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h428 | h428
                    · linarith only [h409, h428, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                      · linarith only [h405, h430, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                        · linarith only [h406, h430, h432, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                          · linarith only [h406, h409, h434, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                            · linarith only [h0, h405, h408, h428, h436, hc01, hlam, hphi, ht12, u2elo0]
                            · rcases h5bigk with h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h0, hlam, p438_1]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h0, h434, hlam, hphi, ht01, ht0b, ht45, ht5b, p438_1, u1elo4, u4ehi2]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h405, h408, h430, h436, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p438_1, u2elo0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h409, hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht5b, p438_1, u1elo4, u5ehi0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h427, h434, hlam, hphi, ht01, ht0b, ht45, ht5b, p438_1, u1elo1, u4ehi2]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h430, h436, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p438_1, u1elo4]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h428, hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h407, hlam, p438_1]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h427, hlam, p438_1]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h432, hlam, p438_1]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h434, hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h408, hlam, p438_1]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p438_1]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h405, h408, h434, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p438_1, u2elo0, u4ehi2]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h436, hlam, p438_0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h407, h434, hc45, hlam, hphi, p438_1, u4ehi2]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h0, h405, h408, h432, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p438_1, u2elo0]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h434, hc45, hlam, hphi, p438_1, u4ehi2]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [h432, h434, hc45, hlam, hphi, p438_1, u4ehi2]
                              · have p438_0 := h438c.1
                                have p438_1 := h438c.2.1
                                have p438_2 := h438c.2.2.1
                                have p438_3 := h438c.2.2.2
                                linarith only [hlam, p438_0]
                  · linarith only [h407, h427, hc12, hlam, hphi, u2elo0]
                · linarith only [h406, h425, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h405, h425, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
            · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
              · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
                      · linarith only [h405, h472, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h474 | h474
                        · linarith only [h406, h408, h472, h474, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h476 | h476
                          · linarith only [h406, h476, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · linarith only [h406, h467, h476, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                    · linarith only [h406, h467, h471, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                  · linarith only [h407, h470, hc12, hlam, hphi, u2elo0]
                · linarith only [h406, h469, hc12, hlam, hphi, u2elo0]
              · linarith only [h405, h468, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
              · rcases m.htr 1 2 4 (by decide) (by decide) with h484 | h484
                · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h467, h486, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h488 | h488
                      · linarith only [h405, h488, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h490 | h490
                        · linarith only [h405, h408, h490, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h492 | h492
                          · linarith only [h406, h467, h492, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h494 | h494
                            · rcases h5bigk with h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h0, hlam, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p495_1, u1elo4, u5ehi2]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h408, hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h467, hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht5b, p495_1, u1elo4, u5ehi0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h485, hlam, hphi, ht01, ht0b, ht5b, p495_1, u1elo1, u5ehi2]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h486, h494, hlam, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h486, hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h407, hlam, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h485, hlam, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h490, hlam, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h492, hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                rcases p495_3 (m.d 0 5) (by simp) with h511 | h511
                                · linarith only [h408, h511, hlam]
                                · rcases p495_3 (m.d 1 5) (by simp) with h513 | h513
                                  · linarith only [h406, h467, h513, hlam, hphi, ht01, ht0b, ht45, ht5b, p495_1, u1elo4, u4ehi2]
                                  · linarith only [h0, h513, hlam]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                rcases p495_3 (m.d 0 5) (by simp) with h517 | h517
                                · linarith only [h408, h517, hlam]
                                · linarith only [h407, h517, hlam]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [hlam, p495_0]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h486, h494, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p495_1, u4ehi1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h406, h467, hc45, hlam, hphi, p495_1, u4ehi2]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h492, hc45, hlam, hphi, p495_1, u4ehi2]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [h494, hlam, p495_1]
                              · have p495_0 := h495c.1
                                have p495_1 := h495c.2.1
                                have p495_2 := h495c.2.2.1
                                have p495_3 := h495c.2.2.2
                                linarith only [hlam, p495_0]
                            · rcases h5bigk with h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h0, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h0, h492, hlam, hphi, ht01, ht0b, ht45, ht5b, p527_1, u1elo4, u4ehi2]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h408, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h467, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo4, u5ehi0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h485, h492, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p527_1, u2elo1, u4ehi2]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h485, hlam, hphi, ht01, ht0b, ht12, ht5b, p527_1, u2elo1, u5ehi3]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h486, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h407, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h485, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h490, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h492, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h407, h492, h494, hc45, hlam, hphi, p527_1, u4ehi2]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h0, h494, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h492, h494, hc45, hlam, hphi, p527_1, u4ehi2]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h494, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h407, h492, hc45, hlam, hphi, p527_1, u4ehi2]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h492, hc45, hlam, hphi, p527_1, u4ehi2]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h408, hc03, hc45, hlam, hphi, ht34, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                  · linarith only [h407, h485, hc12, hlam, hphi, u2elo0]
                · linarith only [h406, h483, h484, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h405, h483, hc12, hlam, hphi, u2elo0]
        · linarith only [h406, h407, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h557 | h557
        · linarith only [h406, h557, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h559 | h559
          · linarith only [h405, h406, h559, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
            · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
              · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
                · linarith only [h405, h406, h563, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h565 | h565
                  · linarith only [h405, h557, h563, h565, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                      · linarith only [h405, h568, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                        · linarith only [h405, h406, h570, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                            · rcases h5bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h0, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h557, hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h559, hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u1elo4, u4ehi4]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht5b, p574_1, u1elo4, u5ehi0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h565, hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h565, h570, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h565, h572, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p574_1, u2elo3, u4ehi4]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h405, h557, h572, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p574_1, u2elo3]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h572, hlam, hphi, ht01, ht0b, ht12, ht5b, p574_1, u2elo3, u5ehi1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h570, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h572, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p574_1, u2elo3, u4ehi4]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h405, h557, hc23, hc35, hlam, hphi, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h0, h573, hc01, hc34, hlam, hphi, ht12, ht23, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h405, h557, h573, hc23, hc34, hlam, hphi, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [hlam, p574_0]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                rcases p574_3 (m.d 0 5) (by simp) with h594 | h594
                                · linarith only [h559, h594, hlam]
                                · linarith only [h561, h594, hlam]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h561, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h567, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h572, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [h573, hlam, p574_1]
                              · have p574_0 := h574c.1
                                have p574_1 := h574c.2.1
                                have p574_2 := h574c.2.2.1
                                have p574_3 := h574c.2.2.2
                                linarith only [hlam, p574_0]
                            · linarith only [h567, h573, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                          · linarith only [h406, h561, h572, hlam]
                    · linarith only [h406, h561, h567, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
              · linarith only [h405, h557, h562, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
              · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
                · linarith only [h405, h406, h607, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h609 | h609
                  · linarith only [h405, h557, h609, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                    · linarith only [h405, h406, h561, h607, h611, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                      · linarith only [h405, h613, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                        · linarith only [h405, h406, h615, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                          · linarith only [h561, h617, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · linarith only [h405, h406, h617, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h405, h406, h606, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h621 | h621
      · linarith only [h405, h621, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h623 | h623
        · linarith only [h405, h623, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h625 | h625
          · rcases m.htr 0 4 5 (by decide) (by decide) with h626 | h626
            · rcases m.htr 1 2 3 (by decide) (by decide) with h627 | h627
              · linarith only [h405, h625, h627, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
                · linarith only [h621, h627, h629, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
                  · linarith only [h623, h627, h631, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h633 | h633
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h635 | h635
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h636 | h636
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h637 | h637
                            · linarith only [h634, h637, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                            · linarith only [h621, h626, h634, h637, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                          · linarith only [h621, h626, h636, hlam]
                        · linarith only [h621, h625, h626, h634, h635, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h642 | h642
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h643 | h643
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h644 | h644
                            · rcases h5bigk with h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c | h645c
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h0, hlam, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h623, hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h0, h644, hlam, hphi, ht01, ht0b, ht45, ht5b, p645_1, u1elo4, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h0, h631, h634, h642, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h631, h634, h642, hlam, hphi, ht01, ht0b, ht12, ht5b, p645_1, u2elo3, u5ehi0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h631, hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h631, h634, h642, h644, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h631, h634, h642, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h625, h634, h642, h644, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h634, h642, hlam, hphi, ht01, ht0b, ht12, ht5b, p645_1, u2elo3, u5ehi1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h634, h642, h644, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h634, h642, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h625, hlam, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h0, h625, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h642, hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [hlam, p645_0]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h405, h625, h634, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p645_1, u2elo3, u4ehi4]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h626, hlam, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h633, hlam, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h643, hlam, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [h644, hlam, p645_1]
                              · have p645_0 := h645c.1
                                have p645_1 := h645c.2.1
                                have p645_2 := h645c.2.2.1
                                have p645_3 := h645c.2.2.2
                                linarith only [hlam, p645_0]
                            · linarith only [h631, h634, h642, h644, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h621, h626, h643, hlam]
                        · linarith only [h405, h625, h642, hlam]
                    · linarith only [h621, h626, h633, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h675 | h675
              · linarith only [h405, h625, h675, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h677 | h677
                · linarith only [h675, h677, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h679 | h679
                  · linarith only [h675, h679, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h681 | h681
                    · linarith only [h626, h681, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h683 | h683
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h684 | h684
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h685 | h685
                          · linarith only [h677, h681, h683, h685, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h687 | h687
                            · linarith only [h683, h685, h687, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                            · rcases h5bigk with h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h0, hlam, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h623, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h0, h687, hlam, hphi, ht01, ht0b, ht45, ht5b, p689_1, u1elo4, u4ehi3]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h626, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, hphi, ht01, ht0b, ht5b, p689_1, u1elo4, u5ehi0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h679, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h679, h684, h687, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p689_1, u2elo2, u4ehi3]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h681, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h625, h684, h687, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p689_1, u2elo2, u4ehi3]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h684, hlam, hphi, ht01, ht0b, ht12, ht5b, p689_1, u2elo2, u5ehi1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h684, h687, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p689_1, u2elo2, u4ehi3]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h685, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h625, hlam, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h0, h625, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h684, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h687, hlam, p689_0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h626, hc45, hlam, hphi, p689_1, u4ehi0]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h623, hc02, hc45, hlam, hphi, ht23, ht34, p689_1]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [h687, hc45, hlam, hphi, p689_1, u4ehi3]
                              · have p689_0 := h689c.1
                                have p689_1 := h689c.2.1
                                have p689_2 := h689c.2.2.1
                                have p689_3 := h689c.2.2.2
                                linarith only [hlam, p689_0]
                        · linarith only [h405, h625, h684, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h716 | h716
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h717 | h717
                          · linarith only [h626, h717, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · linarith only [h683, h716, h717, hlam]
                        · linarith only [h405, h625, h716, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h721 | h721
            · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
              · linarith only [h405, h722, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
                · linarith only [h621, h721, h724, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h726 | h726
                  · linarith only [h722, h726, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h730 | h730
                        · linarith only [h405, h625, h730, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h732 | h732
                          · linarith only [h729, h730, h732, hlam]
                          · linarith only [h621, h721, h732, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
                        · linarith only [h405, h625, h735, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h737 | h737
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                            · rcases h5bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h0, hlam, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h623, hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h625, hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h0, h724, h728, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p739_1, u2elo3, u4ehi4]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h724, h728, hlam, hphi, ht01, ht0b, ht12, ht5b, p739_1, u2elo3, u5ehi0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h726, hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h722, h724, h728, h735, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p739_1, u2elo3]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h724, h728, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p739_1, u2elo3, u4ehi4]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h721, h737, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p739_1, u2elo3, u4ehi4]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h737, hlam, hphi, ht01, ht0b, ht12, ht5b, p739_1, u2elo3, u5ehi1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h735, hlam, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h737, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p739_1, u2elo3, u4ehi4]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                rcases p739_3 (m.d 0 5) (by simp) with h755 | h755
                                · linarith only [h625, h755, hlam]
                                · rcases p739_3 (m.d 1 5) (by simp) with h757 | h757
                                  · linarith only [h721, h757, hlam, hphi, ht01, ht0b, ht45, ht5b, p739_1, u1elo4, u4ehi4]
                                  · linarith only [h0, h757, hlam]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h0, h738, hc01, hc34, hlam, hphi, ht12, ht23, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h623, h738, hc02, hc34, hlam, hphi, ht23, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [hlam, p739_0]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                rcases p739_3 (m.d 0 5) (by simp) with h763 | h763
                                · linarith only [h625, h763, hlam]
                                · linarith only [h721, h763, hlam]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h721, hlam, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h728, hlam, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h737, hlam, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [h738, hlam, p739_1]
                              · have p739_0 := h739c.1
                                have p739_1 := h739c.2.1
                                have p739_2 := h739c.2.2.1
                                have p739_3 := h739c.2.2.2
                                linarith only [hlam, p739_0]
                            · linarith only [h621, h721, h738, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                          · linarith only [h621, h721, h737, hlam]
                    · linarith only [h621, h721, h728, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h774 | h774
              · linarith only [h405, h774, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h776 | h776
                · linarith only [h774, h776, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h778 | h778
                  · linarith only [h776, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
                    · linarith only [h721, h780, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h782 | h782
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h783 | h783
                        · linarith only [h405, h625, h783, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h785 | h785
                          · linarith only [h776, h780, h782, h783, h785, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h787 | h787
                            · linarith only [h782, h783, h785, h787, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h782, h783, h787, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h790 | h790
                        · linarith only [h405, h625, h790, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h792 | h792
                          · linarith only [h721, h792, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h794 | h794
                            · linarith only [h405, h782, h792, h794, hc02, hc34, hlam, hphi, ht23]
                            · linarith only [h405, h782, h794, hc02, hc45, hlam, hphi, ht23, ht34]

end R2N4
