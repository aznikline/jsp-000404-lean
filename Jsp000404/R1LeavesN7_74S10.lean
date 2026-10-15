import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_15_H_L_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h6, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h2, h5, h8, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h10, h2, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, h2, h5, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h1, h15, h2, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h1, h17, h2, h4, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
          · rcases m.htr 0 2 5 (by decide) (by decide) with h21 | h21
            · linarith only [h21, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h2, h20, h23, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h2, h25, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h2, h27, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · linarith only [h20, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h30 | h30
            · linarith only [h1, h2, h20, h30, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
              · linarith only [h1, h2, h32, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h2, h34, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                  · linarith only [h0, h2, h20, h36, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h1, h2, h30, h36, h38, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                      · linarith only [h1, h2, h32, h40, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                            · linarith only [h1, h2, h36, h40, h44, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                              · linarith only [h0, h20, h42, h44, h46, hc12, hc23, hlam, hphi]
                              · rcases h2bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h4, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h20, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h30, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h0, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h34, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h36, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h38, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  rcases p48_3 (m.d 0 2) (by simp) with h59 | h59
                                  · linarith only [h59, hlam, p48_0]
                                  · rcases p48_3 (m.d 1 2) (by simp) with h61 | h61
                                    · linarith only [h34, h61, hlam]
                                    · rcases p48_3 (m.d 2 3) (by simp) with h63 | h63
                                      · rcases p48_3 (m.d 2 4) (by simp) with h64 | h64
                                        · linarith only [h42, h64, hlam]
                                        · linarith only [h20, h64, hlam]
                                      · linarith only [h63, hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  rcases p48_3 (m.d 0 2) (by simp) with h68 | h68
                                  · linarith only [h4, h68, hlam]
                                  · linarith only [h0, h68, hlam]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h20, hc02, hc23, hlam, hphi, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h1, h2, h36, h38, hc12, hc23, hlam, hphi, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h0, h44, hc12, hc45, hlam, hphi, ht23, ht34, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h44, hc12, hc45, hlam, hphi, ht23, ht34, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h42, hlam, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [hlam, p48_0]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h44, hlam, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  rcases p48_3 (m.d 0 2) (by simp) with h79 | h79
                                  · linarith only [h79, hlam, p48_0]
                                  · rcases p48_3 (m.d 1 2) (by simp) with h81 | h81
                                    · linarith only [h38, h81, hlam]
                                    · rcases p48_3 (m.d 2 3) (by simp) with h83 | h83
                                      · rcases p48_3 (m.d 2 4) (by simp) with h84 | h84
                                        · linarith only [h44, h84, hlam]
                                        · linarith only [h20, h84, hlam]
                                      · linarith only [h4, h83, hlam]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  rcases p48_3 (m.d 0 2) (by simp) with h88 | h88
                                  · linarith only [h30, h88, hlam]
                                  · linarith only [h0, h88, hlam]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h43, hlam, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [h0, h20, hc12, hc25, hlam, hphi, p48_1]
                                · have p48_0 := h48c.1
                                  have p48_1 := h48c.2.1
                                  have p48_2 := h48c.2.2.1
                                  have p48_3 := h48c.2.2.2
                                  linarith only [hlam, p48_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h1, h2, h36, h40, h94, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                              · linarith only [h42, h43, h94, h96, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · rcases h2bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u0elo1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h4, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h20, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h30, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h0, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h34, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h36, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h38, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h43, h96, hc02, hc45, hlam, hphi, ht23, ht34, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h43, h96, hc12, hc45, hlam, hphi, ht23, ht34, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h43, h96, hc24, hc45, hlam, hphi, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h43, hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h0, h42, h43, h96, hc12, hc45, hlam, hphi, ht23, ht34, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h42, h43, h96, hc12, hc45, hlam, hphi, ht23, ht34, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h42, hlam, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [hlam, p98_0]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h94, hlam, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  rcases p98_3 (m.d 0 2) (by simp) with h119 | h119
                                  · linarith only [h119, hlam, p98_0]
                                  · rcases p98_3 (m.d 1 2) (by simp) with h121 | h121
                                    · linarith only [h121, h38, hlam]
                                    · rcases p98_3 (m.d 2 3) (by simp) with h123 | h123
                                      · linarith only [h123, h43, hlam]
                                      · linarith only [h123, h4, hlam]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  rcases p98_3 (m.d 0 2) (by simp) with h126 | h126
                                  · linarith only [h126, h30, hlam]
                                  · linarith only [h0, h126, hlam]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h0, h4, hc12, hc25, hlam, hphi, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [h0, h20, h43, h96, hc12, hc45, hlam, hphi, ht23, ht34, p98_1]
                                · have p98_0 := h98c.1
                                  have p98_1 := h98c.2.1
                                  have p98_2 := h98c.2.2.1
                                  have p98_3 := h98c.2.2.2
                                  linarith only [hlam, p98_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                          · linarith only [h1, h132, h2, h36, h38, h42, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                            · linarith only [h1, h134, h2, h36, h40, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                              · linarith only [h0, h134, h136, h4, h42, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h136, h4, h42, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h139 | h139
      · linarith only [h139, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h141 | h141
        · rcases m.htr 0 2 4 (by decide) (by decide) with h142 | h142
          · linarith only [h0, h1, h142, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h144 | h144
            · linarith only [h0, h1, h144, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
              · linarith only [h146, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                · linarith only [h0, h1, h146, h148, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h1, h141, h146, h148, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h151 | h151
          · linarith only [h0, h1, h151, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h153 | h153
            · linarith only [h0, h153, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
              · linarith only [h155, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
                · linarith only [h0, h1, h141, h155, h157, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                  · linarith only [h0, h1, h151, h159, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                    · linarith only [h0, h1, h153, h155, h161, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h0, h1, h155, h159, h163, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h1, h163, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h166 | h166
    · rcases m.htr 0 1 5 (by decide) (by decide) with h167 | h167
      · linarith only [h167, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h169 | h169
        · rcases m.htr 0 2 4 (by decide) (by decide) with h170 | h170
          · rcases m.htr 0 2 5 (by decide) (by decide) with h171 | h171
            · linarith only [h171, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h173 | h173
              · linarith only [h0, h166, h171, h173, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h177 | h177
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h166, h171, h173, h178, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                        · linarith only [h169, h171, h180, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                          · linarith only [h0, h166, h171, h176, h180, h182, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                            · linarith only [h0, h166, h171, h176, h177, h178, h184, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                              · linarith only [h0, h166, h171, h176, h177, h178, h180, h186, hc23, hc34, hlam, hphi]
                              · rcases h2bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h0, hlam, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h171, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u0elo4]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h171, hc24, hlam, hphi, ht0b, ht45, ht5b, p188_1, u0elo4]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h171, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  rcases p188_3 (m.d 0 2) (by simp) with h194 | h194
                                  · linarith only [h0, h194, hlam]
                                  · rcases p188_3 (m.d 1 2) (by simp) with h196 | h196
                                    · rcases p188_3 (m.d 2 3) (by simp) with h197 | h197
                                      · linarith only [h175, h197, hlam]
                                      · rcases p188_3 (m.d 2 4) (by simp) with h199 | h199
                                        · linarith only [h176, h199, hlam]
                                        · rcases p188_3 (m.d 2 5) (by simp) with h201 | h201
                                          · linarith only [h177, h201, hlam]
                                          · linarith only [h171, h201, hlam]
                                    · linarith only [h0, h196, hlam]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h169, h171, h177, hlam, p188_2]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h170, h171, h177, hlam, p188_2]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h0, h171, hc01, hc12, hlam, hphi, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h169, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h175, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h180, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h182, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h170, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h176, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u0elo1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h184, hlam, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h169, h182, hc23, hc35, hlam, hphi, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h177, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  rcases p188_3 (m.d 0 2) (by simp) with h221 | h221
                                  · linarith only [h171, h221, hlam]
                                  · linarith only [h169, h221, hlam]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  rcases p188_3 (m.d 0 2) (by simp) with h224 | h224
                                  · linarith only [h171, h224, hlam]
                                  · linarith only [h170, h224, hlam]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                      · linarith only [h166, h228, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                        · linarith only [h169, h171, h230, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h0, h166, h176, h177, h230, h232, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · linarith only [h0, h166, h176, h177, h230, h232, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h170, h171, h176, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h166, h169, h171, h175, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
          · linarith only [h0, h166, h170, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h238 | h238
          · rcases m.htr 0 2 5 (by decide) (by decide) with h239 | h239
            · linarith only [h169, h239, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
              · linarith only [h0, h166, h169, h241, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                      · linarith only [h0, h166, h169, h241, h246, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                            · linarith only [h166, h244, h246, h250, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                              · linarith only [h0, h239, h243, h245, h246, h248, h252, hc01, hc12, hlam, hphi]
                              · rcases h2bigk with h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h169, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h248, hc34, hlam, hphi, ht0b, ht45, ht5b, p254_1, u0elo1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h239, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  rcases p254_3 (m.d 0 2) (by simp) with h260 | h260
                                  · linarith only [h0, h260, hlam]
                                  · rcases p254_3 (m.d 1 2) (by simp) with h262 | h262
                                    · rcases p254_3 (m.d 2 3) (by simp) with h263 | h263
                                      · linarith only [h243, h263, hlam]
                                      · linarith only [h169, h263, hlam]
                                    · linarith only [h0, h262, hlam]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h249, hc12, hlam, hphi, ht01, ht0b, ht5b, p254_1, u5ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h166, h239, h243, h244, h249, hlam, p254_2]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h166, h239, h244, h248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h166, h243, h244, h248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h243, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  rcases p254_3 (m.d 0 2) (by simp) with h274 | h274
                                  · linarith only [h169, h274, hlam]
                                  · linarith only [h238, h274, hlam]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h166, h239, h243, h244, h248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h238, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h244, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h248, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h250, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, h166, h244, h245, h246, h248, hc34, hc45, hlam, hphi, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h245, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h249, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  rcases p254_3 (m.d 0 2) (by simp) with h286 | h286
                                  · linarith only [h239, h286, hlam]
                                  · linarith only [h238, h286, hlam]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h290 | h290
                            · linarith only [h166, h244, h246, h290, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
                              · linarith only [h0, h166, h169, h244, h245, h246, h248, h249, h292, hlam]
                              · linarith only [h0, h166, h169, h244, h248, h249, h292, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h166, h169, h244, h248, hlam]
                    · linarith only [h0, h166, h169, h243, h244, h245, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h169, h243, h244, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h0, h166, h239, h243, h298, h299, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                      · linarith only [h166, h301, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h0, h166, h298, h299, h301, h304, h305, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                            · linarith only [h0, h166, h298, h299, h303, h305, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h166, h243, h298, h303, h304, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h243, h303, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h166, h169, h238, h298, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · linarith only [h0, h166, h238, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
      · linarith only [h312, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h314 | h314
        · rcases m.htr 0 2 4 (by decide) (by decide) with h315 | h315
          · rcases m.htr 0 2 5 (by decide) (by decide) with h316 | h316
            · linarith only [h316, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
              · linarith only [h315, h316, h318, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                · rcases m.htr 1 2 4 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h322 | h322
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                        · linarith only [h314, h316, h324, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h326 | h326
                          · linarith only [h315, h316, h324, h326, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h328 | h328
                            · linarith only [h166, h315, h316, h318, h328, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                              · linarith only [h315, h316, h324, h328, h330, hc23, hc34, hlam, hphi]
                              · rcases h2bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h0, hlam, p332_1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h316, h321, h323, h326, h330, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p332_1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h316, h321, h323, h326, h330, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p332_1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h316, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  rcases p332_3 (m.d 0 2) (by simp) with h338 | h338
                                  · linarith only [h0, h338, hlam]
                                  · rcases p332_3 (m.d 1 2) (by simp) with h340 | h340
                                    · rcases p332_3 (m.d 2 3) (by simp) with h341 | h341
                                      · linarith only [h320, h341, hlam]
                                      · rcases p332_3 (m.d 2 4) (by simp) with h343 | h343
                                        · linarith only [h321, h343, hlam]
                                        · rcases p332_3 (m.d 2 5) (by simp) with h345 | h345
                                          · linarith only [h322, h345, hlam]
                                          · linarith only [h316, h345, hlam]
                                    · linarith only [h0, h340, hlam]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h314, h316, h321, h323, h326, h330, hlam, p332_2]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h315, h316, h321, h323, h326, h330, hlam, p332_2]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h315, h316, h324, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p332_1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h314, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h320, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h324, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h326, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h315, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h321, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h315, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p332_1, u0elo1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h328, hlam, p332_1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h315, h322, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p332_1]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [h322, hlam, p332_0]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  rcases p332_3 (m.d 0 2) (by simp) with h365 | h365
                                  · linarith only [h316, h365, hlam]
                                  · linarith only [h314, h365, hlam]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  rcases p332_3 (m.d 0 2) (by simp) with h368 | h368
                                  · linarith only [h316, h368, hlam]
                                  · linarith only [h315, h368, hlam]
                                · have p332_0 := h332c.1
                                  have p332_1 := h332c.2.1
                                  have p332_2 := h332c.2.2.1
                                  have p332_3 := h332c.2.2.2
                                  linarith only [hlam, p332_0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                        · linarith only [h314, h372, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                          · linarith only [h315, h316, h372, h374, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h376 | h376
                            · linarith only [h315, h316, h323, h376, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h378 | h378
                              · linarith only [h315, h316, h322, h323, h372, h378, hc23, hc34, hlam, hphi]
                              · rcases h2bigk with h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h0, hlam, p380_1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u0elo1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h372, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u0elo1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h316, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  rcases p380_3 (m.d 0 2) (by simp) with h386 | h386
                                  · linarith only [h0, h386, hlam]
                                  · rcases p380_3 (m.d 1 2) (by simp) with h388 | h388
                                    · rcases p380_3 (m.d 2 3) (by simp) with h389 | h389
                                      · linarith only [h320, h389, hlam]
                                      · rcases p380_3 (m.d 2 4) (by simp) with h391 | h391
                                        · linarith only [h321, h391, hlam]
                                        · rcases p380_3 (m.d 2 5) (by simp) with h393 | h393
                                          · linarith only [h322, h393, hlam]
                                          · linarith only [h316, h393, hlam]
                                    · linarith only [h0, h388, hlam]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h315, h316, h322, h372, hlam, p380_2]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h315, h316, h322, hlam, p380_2]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h315, h316, h372, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p380_1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h314, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h320, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h372, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h374, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h315, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h321, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h315, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u0elo1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h376, hlam, p380_1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h314, h374, hc23, hc35, hlam, hphi, p380_1]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [h322, hlam, p380_0]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  rcases p380_3 (m.d 0 2) (by simp) with h413 | h413
                                  · linarith only [h316, h413, hlam]
                                  · linarith only [h314, h413, hlam]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  rcases p380_3 (m.d 0 2) (by simp) with h416 | h416
                                  · linarith only [h316, h416, hlam]
                                  · linarith only [h315, h416, hlam]
                                · have p380_0 := h380c.1
                                  have p380_1 := h380c.2.1
                                  have p380_2 := h380c.2.2.1
                                  have p380_3 := h380c.2.2.2
                                  linarith only [hlam, p380_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                      · linarith only [h166, h318, h321, h322, h420, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
                        · linarith only [h314, h422, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h424 | h424
                          · linarith only [h315, h316, h422, h424, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h426 | h426
                            · linarith only [h166, h315, h316, h420, h426, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h428 | h428
                              · linarith only [h0, h322, h426, h428, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h2bigk with h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, hlam, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h316, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p430_1, u0elo4]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h316, hc24, hlam, hphi, ht0b, ht45, ht5b, p430_1, u0elo4]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h316, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h322, h424, h428, hc02, hc45, hlam, hphi, ht23, ht34, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h322, h424, h428, hc23, hc45, hlam, hphi, ht34, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h322, h424, h428, hc24, hc45, hlam, hphi, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h322, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h314, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h320, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h422, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h424, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h315, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h321, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h315, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p430_1, u0elo1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h426, hlam, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h315, h424, h428, hc24, hc45, hlam, hphi, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h166, h321, h424, h428, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 2) (by simp) with h453 | h453
                                  · linarith only [h316, h453, hlam]
                                  · linarith only [h314, h453, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 2) (by simp) with h456 | h456
                                  · linarith only [h316, h456, hlam]
                                  · linarith only [h315, h456, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                  · linarith only [h315, h321, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h314, h320, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h462 | h462
            · linarith only [h315, h462, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h464 | h464
              · linarith only [h464, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
                · rcases m.htr 1 2 4 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h469 | h469
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                        · linarith only [h314, h315, h464, h467, h469, h470, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                          · linarith only [h314, h315, h464, h467, h469, h472, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                            · linarith only [h314, h315, h464, h470, h474, hc23, hc34, hlam, hphi]
                            · linarith only [h314, h315, h467, h469, h474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h314, h315, h467, h469, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h314, h315, h467, h468, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                    · linarith only [h314, h462, h467, h479, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
                        · linarith only [h314, h482, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h314, h315, h464, h467, h481, h482, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h485 | h485
                        · linarith only [h314, h485, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h487 | h487
                          · linarith only [h314, h315, h464, h487, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                            · linarith only [h0, h467, h481, h485, h489, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h314, h315, h489, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h314, h466, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h493 | h493
          · rcases m.htr 0 2 5 (by decide) (by decide) with h494 | h494
            · linarith only [h314, h494, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h496 | h496
              · linarith only [h496, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
                · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h503 | h503
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h504 | h504
                            · linarith only [h493, h494, h496, h498, h503, h504, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h506 | h506
                              · linarith only [h493, h494, h502, h504, h506, hlam]
                              · rcases h2bigk with h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h0, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h314, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h494, h499, h501, h504, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h494, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 2) (by simp) with h514 | h514
                                  · linarith only [h0, h514, hlam]
                                  · rcases p508_3 (m.d 1 2) (by simp) with h516 | h516
                                    · rcases p508_3 (m.d 2 3) (by simp) with h517 | h517
                                      · linarith only [h498, h517, hlam]
                                      · linarith only [h314, h517, hlam]
                                    · linarith only [h0, h516, hlam]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h503, hc12, hlam, hphi, ht01, ht0b, ht5b, p508_1, u5ehi3]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h493, h494, h499, h501, h504, hlam, p508_2]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h493, h494, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h493, h498, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h498, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 2) (by simp) with h528 | h528
                                  · linarith only [h314, h528, hlam]
                                  · linarith only [h493, h528, hlam]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h493, h494, h498, h502, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h493, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h499, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h502, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h504, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h493, h500, h502, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h500, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h503, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 2) (by simp) with h540 | h540
                                  · linarith only [h494, h540, hlam]
                                  · linarith only [h493, h540, hlam]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                            · linarith only [h493, h544, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h546 | h546
                              · linarith only [h502, h503, h544, h546, hlam]
                              · linarith only [h314, h493, h499, h501, h503, h546, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h314, h493, h502, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h551 | h551
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h552 | h552
                            · linarith only [h493, h501, h552, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h554 | h554
                              · linarith only [h166, h501, h554, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h2bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h0, hlam, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h314, hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h494, h498, h551, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h494, hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  rcases p556_3 (m.d 0 2) (by simp) with h562 | h562
                                  · linarith only [h0, h562, hlam]
                                  · rcases p556_3 (m.d 1 2) (by simp) with h564 | h564
                                    · rcases p556_3 (m.d 2 3) (by simp) with h565 | h565
                                      · linarith only [h498, h565, hlam]
                                      · linarith only [h314, h565, hlam]
                                    · linarith only [h0, h564, hlam]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h551, hc12, hlam, hphi, ht01, ht0b, ht5b, p556_1, u5ehi3]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h493, h494, h498, h551, hlam, p556_2]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h493, h494, h550, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h493, h498, h550, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h498, hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  rcases p556_3 (m.d 0 2) (by simp) with h576 | h576
                                  · linarith only [h314, h576, hlam]
                                  · linarith only [h493, h576, hlam]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h493, h494, h498, h550, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h493, hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h499, hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h550, hlam, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h552, hlam, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h493, h500, h550, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h500, hlam, p556_0]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [h551, hlam, p556_1]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  rcases p556_3 (m.d 0 2) (by simp) with h588 | h588
                                  · linarith only [h494, h588, hlam]
                                  · linarith only [h493, h588, hlam]
                                · have p556_0 := h556c.1
                                  have p556_1 := h556c.2.1
                                  have p556_2 := h556c.2.2.1
                                  have p556_3 := h556c.2.2.2
                                  linarith only [hlam, p556_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h592 | h592
                            · linarith only [h493, h501, h592, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h594 | h594
                              · linarith only [h166, h314, h493, h501, h550, h551, h594, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h314, h493, h550, h551, h594, hc34, hc45, hlam, hphi]
                        · linarith only [h314, h493, h550, hlam]
                    · linarith only [h314, h498, h500, hc02, hc25, hlam, hphi]
                  · linarith only [h314, h493, h498, h499, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
                    · linarith only [h493, h494, h498, h601, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
                      · linarith only [h166, h496, h498, h600, h603, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h607 | h607
                            · linarith only [h493, h603, h607, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h609 | h609
                              · linarith only [h0, h601, h607, h609, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h2bigk with h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h0, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h314, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h314, hc24, hlam, hphi, ht0b, ht45, ht5b, p611_1, u0elo2]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h494, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h601, hc02, hc25, hlam, hphi, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h498, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h601, h605, h607, hc34, hc45, hlam, hphi, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h601, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  rcases p611_3 (m.d 0 2) (by simp) with h622 | h622
                                  · linarith only [h622, hlam, p611_0]
                                  · rcases p611_3 (m.d 1 2) (by simp) with h624 | h624
                                    · linarith only [h498, h624, hlam]
                                    · linarith only [h0, h624, hlam]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  rcases p611_3 (m.d 0 2) (by simp) with h629 | h629
                                  · linarith only [h314, h629, hlam]
                                  · linarith only [h493, h629, hlam]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h493, h494, h605, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h493, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h600, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h605, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h607, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h493, h605, h607, hc34, hc45, hlam, hphi, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h166, h600, hc01, hc25, hlam, hphi, ht12, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h606, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  rcases p611_3 (m.d 0 2) (by simp) with h641 | h641
                                  · linarith only [h494, h641, hlam]
                                  · linarith only [h493, h641, hlam]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                          · linarith only [h166, h498, h600, h606, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h166, h498, h600, h605, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h493, h600, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h648 | h648
            · linarith only [h314, h648, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h650 | h650
              · linarith only [h650, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h654 | h654
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h655 | h655
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h657 | h657
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h658 | h658
                            · linarith only [h0, h493, h650, h652, h656, h658, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h493, h655, h658, hc01, hc14, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                            · linarith only [h0, h493, h650, h653, h661, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h493, h653, h655, h661, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h665 | h665
                            · linarith only [h0, h493, h650, h653, h665, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h493, h653, h655, h665, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h668 | h668
                            · linarith only [h0, h493, h650, h653, h668, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h493, h653, h655, h668, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h672 | h672
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h673 | h673
                            · linarith only [h166, h655, h673, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                              · linarith only [h0, h493, h653, h655, h671, h675, hc01, hc23, hlam, hphi, ht12]
                              · rcases h2bigk with h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h314, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h493, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h648, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  rcases p677_3 (m.d 0 2) (by simp) with h683 | h683
                                  · linarith only [h0, h683, hlam]
                                  · rcases p677_3 (m.d 1 2) (by simp) with h685 | h685
                                    · rcases p677_3 (m.d 2 3) (by simp) with h686 | h686
                                      · linarith only [h652, h686, hlam]
                                      · linarith only [h314, h686, hlam]
                                    · linarith only [h0, h685, hlam]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h672, hc12, hlam, hphi, ht01, ht0b, ht5b, p677_1, u5ehi3]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h493, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h648, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h652, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h652, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h493, h652, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h648, h652, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h653, h655, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h653, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h671, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h673, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h654, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h654, hlam, p677_0]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h672, hlam, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [h0, h493, h652, h672, hc01, hc12, hlam, hphi, p677_1]
                                · have p677_0 := h677c.1
                                  have p677_1 := h677c.2.1
                                  have p677_2 := h677c.2.2.1
                                  have p677_3 := h677c.2.2.2
                                  linarith only [hlam, p677_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h709 | h709
                            · linarith only [h166, h655, h709, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h711 | h711
                              · linarith only [h0, h493, h653, h655, h711, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h2bigk with h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, hlam, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h314, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h493, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h648, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  rcases p713_3 (m.d 0 2) (by simp) with h719 | h719
                                  · linarith only [h0, h719, hlam]
                                  · rcases p713_3 (m.d 1 2) (by simp) with h721 | h721
                                    · rcases p713_3 (m.d 2 3) (by simp) with h722 | h722
                                      · linarith only [h652, h722, hlam]
                                      · linarith only [h314, h722, hlam]
                                    · linarith only [h0, h721, hlam]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h314, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h493, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h648, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h652, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h652, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h493, h652, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h672, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h653, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h653, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h671, hlam, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h709, hlam, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h654, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h654, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h654, h671, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h493, h654, hc01, hc12, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h745 | h745
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                            · linarith only [h653, h655, h746, hlam]
                            · linarith only [h671, h745, h746, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h749 | h749
                            · linarith only [h653, h655, h749, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h751 | h751
                              · linarith only [h166, h655, h751, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h314, h671, h751, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h314, h652, h654, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h314, h652, h653, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h756 | h756
                  · linarith only [h0, h493, h652, h756, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h758 | h758
                    · linarith only [h0, h648, h652, h758, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h760 | h760
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h761 | h761
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h762 | h762
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h763 | h763
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h764 | h764
                              · linarith only [h0, h493, h650, h761, h764, hc01, hc23, hlam, hphi, ht12]
                              · rcases h2bigk with h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, hlam, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h314, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h493, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h648, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, h758, h761, h763, hc01, hc23, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h652, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h756, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h758, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  rcases p766_3 (m.d 0 2) (by simp) with h777 | h777
                                  · linarith only [h777, hlam, p766_0]
                                  · rcases p766_3 (m.d 1 2) (by simp) with h779 | h779
                                    · linarith only [h652, h779, hlam]
                                    · linarith only [h0, h779, hlam]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, h493, hc01, hc23, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, h758, hc01, hc23, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  rcases p766_3 (m.d 0 2) (by simp) with h786 | h786
                                  · linarith only [h786, hlam, p766_0]
                                  · rcases p766_3 (m.d 1 2) (by simp) with h788 | h788
                                    · linarith only [h756, h788, hlam]
                                    · linarith only [h0, h788, hlam]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h761, hlam, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, h758, h761, hc01, hc23, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  rcases p766_3 (m.d 0 2) (by simp) with h795 | h795
                                  · linarith only [h795, hlam, p766_0]
                                  · rcases p766_3 (m.d 1 2) (by simp) with h797 | h797
                                    · linarith only [h758, h797, hlam]
                                    · linarith only [h0, h797, hlam]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h762, hlam, p766_1]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [h763, hlam, p766_0]
                                · have p766_0 := h766c.1
                                  have p766_1 := h766c.2.1
                                  have p766_2 := h766c.2.2.1
                                  have p766_3 := h766c.2.2.2
                                  linarith only [hlam, p766_0]
                            · linarith only [h0, h493, h760, h763, hc01, hc14, hlam, hphi]
                          · linarith only [h0, h493, h650, h756, h760, h761, h762, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h652, h761, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h807 | h807
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h808 | h808
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h809 | h809
                            · linarith only [h166, h760, h807, h809, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h756, h809, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h652, h808, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h652, h807, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
