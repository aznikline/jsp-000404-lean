import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_13_25_L_0_L_I_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · linarith only [h1, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h1, h10, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h1, h12, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                  · linarith only [h12, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
              · linarith only [h16, h17, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                · linarith only [h1, h19, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                · linarith only [h16, h19, h4, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
              · linarith only [h22, h3, h4, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                · linarith only [h16, h24, h3, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                  · rcases h3bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      rcases p27_3 (m.d 0 3) (by simp) with h29 | h29
                      · rcases p27_3 (m.d 1 3) (by simp) with h30 | h30
                        · linarith only [h0, h30, hlam]
                        · rcases p27_3 (m.d 2 3) (by simp) with h32 | h32
                          · linarith only [h1, h32, hlam]
                          · rcases p27_3 (m.d 3 4) (by simp) with h34 | h34
                            · rcases p27_3 (m.d 3 5) (by simp) with h35 | h35
                              · linarith only [h2, h35, hlam]
                              · linarith only [h16, h35, hlam]
                            · linarith only [h34, h4, hlam]
                      · linarith only [h0, h29, hlam]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      rcases p27_3 (m.d 0 3) (by simp) with h40 | h40
                      · rcases p27_3 (m.d 1 3) (by simp) with h41 | h41
                        · linarith only [h0, h41, hlam]
                        · linarith only [h3, h41, hlam]
                      · linarith only [h1, h40, hlam]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h1, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p27_1, u2elo0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h1, h16, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p27_1, u2elo0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h0, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h4, hc23, hc34, hlam, hphi, p27_1]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h4, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h16, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h1, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h3, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h22, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h24, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h16, h2, hc13, hc34, hlam, hphi, p27_1]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      rcases p27_3 (m.d 0 3) (by simp) with h58 | h58
                      · rcases p27_3 (m.d 1 3) (by simp) with h59 | h59
                        · linarith only [h59, hlam, p27_0]
                        · rcases p27_3 (m.d 2 3) (by simp) with h61 | h61
                          · linarith only [h22, h61, hlam]
                          · rcases p27_3 (m.d 3 4) (by simp) with h63 | h63
                            · rcases p27_3 (m.d 3 5) (by simp) with h64 | h64
                              · linarith only [h26, h64, hlam]
                              · linarith only [h16, h64, hlam]
                            · linarith only [h63, hlam, p27_0]
                      · linarith only [h0, h58, hlam]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      rcases p27_3 (m.d 0 3) (by simp) with h69 | h69
                      · rcases p27_3 (m.d 1 3) (by simp) with h70 | h70
                        · linarith only [h4, h70, hlam]
                        · linarith only [h3, h70, hlam]
                      · linarith only [h1, h69, hlam]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h16, h3, hc23, hc34, hlam, hphi, p27_1]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h2, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h3, hc23, hlam, hphi, ht34, ht45, p27_1, u5elo3]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h1, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p27_1, u2elo0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [h26, hlam, p27_0]
                    · have p27_0 := h27c.1
                      have p27_1 := h27c.2.1
                      have p27_2 := h27c.2.2.1
                      have p27_3 := h27c.2.2.2
                      linarith only [hlam, p27_0]
                  · linarith only [h26, h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
        · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
          · linarith only [h0, h2, h84, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
            · linarith only [h0, h2, h86, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h84, h88, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                · linarith only [h0, h2, h83, h90, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                  · rcases h3bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h2, hc13, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h2, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h2, h92, hlam, hphi, p93_1, u5ehi9, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h2, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h0, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h0, h2, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h84, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h86, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h1, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h83, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h88, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h90, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      rcases p93_3 (m.d 0 3) (by simp) with h109 | h109
                      · linarith only [h109, hlam, p93_0]
                      · rcases p93_3 (m.d 1 3) (by simp) with h111 | h111
                        · linarith only [h111, h84, hlam]
                        · rcases p93_3 (m.d 2 3) (by simp) with h113 | h113
                          · linarith only [h113, h88, hlam]
                          · rcases p93_3 (m.d 3 4) (by simp) with h115 | h115
                            · rcases p93_3 (m.d 3 5) (by simp) with h116 | h116
                              · linarith only [h116, h92, hlam]
                              · linarith only [h116, h2, hlam]
                            · linarith only [h115, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      rcases p93_3 (m.d 0 3) (by simp) with h120 | h120
                      · linarith only [h120, h2, hc13, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                      · linarith only [h0, h120, hlam]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      rcases p93_3 (m.d 0 3) (by simp) with h123 | h123
                      · linarith only [h123, h2, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                      · linarith only [h1, h123, hlam]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h2, hc03, hc34, hlam, hphi, p93_1]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hc03, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h83, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hc23, hlam, hphi, ht34, ht45, p93_1, u5elo3]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [h92, hlam, p93_0]
                    · have p93_0 := h93c.1
                      have p93_1 := h93c.2.1
                      have p93_2 := h93c.2.2.1
                      have p93_3 := h93c.2.2.2
                      linarith only [hlam, p93_0]
                  · linarith only [h83, h84, h92, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h1, h83, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h135 | h135
      · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
        · linarith only [h1, h136, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
          · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
            · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
              · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h0, h1, h138, h142, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                  · rcases h3bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h1, h136, hc12, hlam, hphi, p144_1, u2elo2]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h1, hlam, p144_1]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      rcases p144_3 (m.d 0 3) (by simp) with h148 | h148
                      · rcases p144_3 (m.d 1 3) (by simp) with h149 | h149
                        · linarith only [h0, h149, hlam]
                        · linarith only [h138, h149, hlam]
                      · linarith only [h148, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2, u5ehi8]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h0, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h136, hlam, p144_1]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      rcases p144_3 (m.d 0 3) (by simp) with h157 | h157
                      · rcases p144_3 (m.d 1 3) (by simp) with h158 | h158
                        · rcases p144_3 (m.d 2 3) (by simp) with h159 | h159
                          · rcases p144_3 (m.d 3 4) (by simp) with h160 | h160
                            · linarith only [h160, hlam, p144_0]
                            · rcases p144_3 (m.d 3 5) (by simp) with h162 | h162
                              · linarith only [h139, h162, hlam]
                              · linarith only [h142, h162, hlam]
                          · linarith only [h140, h159, hlam]
                        · linarith only [h158, hlam, p144_0]
                      · linarith only [h0, h157, hlam, p144_1]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2, u5ehi8]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h1, hc02, hlam, hphi, p144_1, u2elo2]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h136, hc12, hlam, hphi, p144_1, u2elo2]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      rcases p144_3 (m.d 0 3) (by simp) with h172 | h172
                      · linarith only [h1, h172, hlam]
                      · linarith only [h0, h138, h172, hlam]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2, u5ehi8]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h0, h139, h142, hlam, hphi, p144_1, u5ehi8, u5elo4]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h138, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h140, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h142, hlam, p144_1]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h135, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h139, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h141, hlam, p144_0]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [h141, hc34, hlam, hphi, ht45, p144_1, u5elo2]
                    · have p144_0 := h144c.1
                      have p144_1 := h144c.2.1
                      have p144_2 := h144c.2.2.1
                      have p144_3 := h144c.2.2.2
                      linarith only [hlam, p144_0]
                · linarith only [h0, h1, h139, h141, hlam]
              · linarith only [h0, h1, h138, h140, hlam]
            · linarith only [h138, h139, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
            · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
              · linarith only [h138, h189, h190, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                  · rcases h3bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h1, h189, h190, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p194_1, u5ehi9]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h1, hlam, p194_1]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h1, h190, hlam, p194_1]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h1, h190, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p194_1, u5ehi9]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h0, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h136, hlam, p194_1]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h138, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h0, h193, hc01, hlam, hphi, ht0b, ht5b, p194_1, u5ehi9]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h190, hc03, hc34, hlam, hphi, p194_1]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h190, hc13, hc34, hlam, hphi, p194_1]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h190, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h190, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p194_1, u5ehi9]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h0, h189, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p194_1, u5ehi9]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h189, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p194_1, u5ehi9]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h1, hc02, hc34, hlam, hphi, ht23, p194_1]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      rcases p194_3 (m.d 0 3) (by simp) with h214 | h214
                      · linarith only [h1, h138, h189, h193, h214, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                      · linarith only [h135, h214, hlam]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h135, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h189, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h192, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [h193, hlam, p194_0]
                    · have p194_0 := h194c.1
                      have p194_1 := h194c.2.1
                      have p194_2 := h194c.2.2.1
                      have p194_3 := h194c.2.2.2
                      linarith only [hlam, p194_0]
                  · linarith only [h1, h190, h193, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h1, h189, h192, hlam]
            · linarith only [h1, h135, h136, h189, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
        · linarith only [h1, h225, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
          · linarith only [h0, h135, h227, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
            · linarith only [h0, h135, h229, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
              · linarith only [h225, h227, h231, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                · linarith only [h135, h231, h233, hc03, hc34, hlam, hphi]
                · linarith only [h1, h233, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h236 | h236
    · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
      · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
        · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
          · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
            · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
              · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
                · linarith only [h236, h242, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                · linarith only [h241, h242, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                · linarith only [h236, h245, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                  · linarith only [h238, h239, h247, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                  · linarith only [h241, h247, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h237, h240, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h251 | h251
            · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
              · linarith only [h0, h237, h239, h252, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h254 | h254
                · linarith only [h236, h254, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                · linarith only [h0, h237, h239, h254, hc23, hc34, hlam, hphi]
            · linarith only [h0, h237, h251, hlam]
        · linarith only [h236, h238, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
        · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
          · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
            · linarith only [h0, h237, h259, h261, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h260, h261, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
            · linarith only [h0, h237, h260, h264, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h264, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
        · linarith only [h236, h259, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
      · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
        · linarith only [h236, h269, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
          · rcases m.htr 1 3 5 (by decide) (by decide) with h272 | h272
            · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
              · rcases m.htr 2 3 5 (by decide) (by decide) with h274 | h274
                · rcases m.htr 3 4 5 (by decide) (by decide) with h275 | h275
                  · linarith only [h269, h271, h275, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                  · rcases h3bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, hlam, p277_1]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h236, hlam, p277_1]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      rcases p277_3 (m.d 0 3) (by simp) with h281 | h281
                      · rcases p277_3 (m.d 1 3) (by simp) with h282 | h282
                        · rcases p277_3 (m.d 2 3) (by simp) with h283 | h283
                          · rcases p277_3 (m.d 3 4) (by simp) with h284 | h284
                            · linarith only [h284, hlam, p277_0]
                            · rcases p277_3 (m.d 3 5) (by simp) with h286 | h286
                              · linarith only [h268, h286, hlam]
                              · linarith only [h275, h286, hlam]
                          · linarith only [h273, h283, hlam]
                        · linarith only [h271, h282, hlam]
                      · linarith only [h281, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, h269, hlam, hphi, ht01, ht0b, ht12, ht5b, p277_1, u2elo2, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, h269, hc01, hlam, hphi, ht12, p277_1, u2elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h269, hlam, p277_1]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      rcases p277_3 (m.d 0 3) (by simp) with h296 | h296
                      · linarith only [h0, h296, hlam]
                      · linarith only [h268, h269, h296, hlam, hphi, ht01, ht0b, ht12, ht5b, p277_1, u2elo2, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h269, hlam, hphi, ht01, ht0b, ht12, ht5b, p277_1, u2elo2, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h268, hlam, hphi, ht01, ht0b, ht12, ht5b, p277_1, u2elo2, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht12, p277_1, u2elo2]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      rcases p277_3 (m.d 0 3) (by simp) with h303 | h303
                      · linarith only [h236, h303, hlam]
                      · linarith only [h268, h303, hlam, hphi, ht01, ht0b, ht12, ht5b, p277_1, u2elo2, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p277_1, u2elo2, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h268, h271, hc14, hlam, hphi, ht01, ht0b, ht5b, p277_1, u5ehi8]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h271, hlam, p277_0]
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
                      linarith only [h275, hlam, p277_1]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h268, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h272, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h274, hlam, p277_0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [h268, hc34, hlam, hphi, ht45, p277_1, u5elo0]
                    · have p277_0 := h277c.1
                      have p277_1 := h277c.2.1
                      have p277_2 := h277c.2.2.1
                      have p277_3 := h277c.2.2.2
                      linarith only [hlam, p277_0]
                · linarith only [h0, h268, h269, h274, hlam]
              · linarith only [h269, h271, h273, hlam]
            · linarith only [h0, h268, h272, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
            · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
              · linarith only [h0, h268, h271, h321, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                  · rcases h3bigk with h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h0, hlam, p325_1]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h236, hlam, p325_1]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h269, h321, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h236, h324, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo2, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h268, h271, h324, hc14, hlam, hphi, ht01, ht0b, ht5b, p325_1, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h269, hlam, p325_1]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h271, hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h269, h321, h324, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo3, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h268, h321, h324, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo3, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h321, hc13, hc34, hlam, hphi, p325_1]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h321, hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h321, h324, hlam, hphi, ht01, ht0b, ht12, ht5b, p325_1, u2elo3, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h268, h324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p325_1, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h0, h268, h324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p325_1, u5ehi9]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h236, hc02, hc34, hlam, hphi, ht23, p325_1]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      rcases p325_3 (m.d 0 3) (by simp) with h345 | h345
                      · linarith only [h0, h271, h345, hlam]
                      · linarith only [h268, h345, hlam]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h268, hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h320, hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h323, hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [h324, hlam, p325_0]
                    · have p325_0 := h325c.1
                      have p325_1 := h325c.2.1
                      have p325_2 := h325c.2.2.1
                      have p325_3 := h325c.2.2.2
                      linarith only [hlam, p325_0]
                  · linarith only [h0, h268, h269, h321, h324, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                · linarith only [h0, h268, h269, h323, hlam]
            · linarith only [h0, h268, h320, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
        · linarith only [h236, h356, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
          · rcases m.htr 1 3 5 (by decide) (by decide) with h359 | h359
            · linarith only [h0, h268, h356, h359, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h358, h359, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
            · linarith only [h0, h268, h358, h362, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h362, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem r1l7_12_13_25_L_R_L_0_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
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
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h13, h16, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                                  · rcases h5bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18_1, u3elo0, u5ehi1]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h4, h6, hlam, hphi, ht23, p18_1, u2ehi4, u3elo0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18_1, u3elo0, u5ehi3]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h16, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p18_1, u3elo0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h1, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p18_1, u2ehi4]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h1, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18_1, u3elo0, u5ehi3]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h1, h16, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p18_1, u3elo0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h3, hlam, p18_1]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h9, hlam, p18_1]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h3, hc02, hlam, hphi, ht0b, ht5b, p18_1, u5ehi3]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h1, h16, h4, h6, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p18_1, u3elo0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h5, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h11, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h14, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h16, hlam, p18_1]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h6, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h12, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h15, hlam, p18_0]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18_1, u3elo0, u5ehi3]
                                    · have p18_0 := h18c.1
                                      have p18_1 := h18c.2.1
                                      have p18_2 := h18c.2.2.1
                                      have p18_3 := h18c.2.2.2
                                      linarith only [hlam, p18_0]
                                · linarith only [h0, h10, h12, h15, hlam, hphi, ht23, u2ehi3, u3elo0]
                              · linarith only [h14, hlam, hphi, ht23, u2ehi2, u3elo4]
                            · linarith only [h13, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h12, h4, h6, h8, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h11, h5, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h7, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h3, h4, h6, h9, hlam, hphi, ht23, u2ehi1, u3elo0]
                  · linarith only [h7, h8, hc24, hlam, hphi, u2ehi2]
                · linarith only [h7, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                          · linarith only [h0, h2, h56, h58, h6, hlam, hphi, ht23, u2ehi3, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                · linarith only [h2, h6, h62, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                  · linarith only [h53, h6, h60, h64, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
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
                                      linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0, u5ehi1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h5, hlam, hphi, ht23, p66_1, u2ehi4, u3elo0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0, u5ehi3]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h6, hlam, p66_1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h1, hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1, u2ehi4]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0, u5ehi3]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h58, hlam, p66_1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h3, hlam, p66_1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h55, hlam, p66_1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h3, hc02, hlam, hphi, ht0b, ht5b, p66_1, u5ehi3]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h62, hlam, p66_1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h5, hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h57, hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h61, hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [hlam, p66_0]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h64, hlam, p66_1]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h3, hc45, hlam, hphi, ht23, ht34, p66_1, u2ehi4]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [h55, hc45, hlam, hphi, ht23, ht34, p66_1, u2ehi4]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht23, ht34, p66_1, u2ehi4]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      rcases p66_3 (m.d 0 5) (by simp) with h90 | h90
                                      · linarith only [h6, h90, hlam]
                                      · linarith only [h5, h90, hlam]
                                    · have p66_0 := h66c.1
                                      have p66_1 := h66c.2.1
                                      have p66_2 := h66c.2.2.1
                                      have p66_3 := h66c.2.2.2
                                      linarith only [hlam, p66_0]
                              · linarith only [h61, hlam, hphi, ht23, u2ehi2, u3elo4]
                            · linarith only [h60, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h5, h57, hc13, hlam, hphi, u3elo0]
                      · linarith only [h53, h56, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h3, h5, h55, hlam, hphi, ht23, u2ehi1, u3elo0]
                  · linarith only [h53, h54, hc24, hlam, hphi, u2ehi2]
                · linarith only [h53, hlam, hphi, ht23, u2ehi1, u3elo2]
            · linarith only [h2, h4, h5, hlam, hphi, ht23, u2ehi3, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h102 | h102
            · linarith only [h102, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                · linarith only [h0, h105, h4, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h105, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                · linarith only [h0, h108, h4, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h108, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h2, h3, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h112 | h112
        · linarith only [h112, h2, hc24, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
          · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
            · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
              · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h1, h112, h114, h116, h119, hlam, hphi, ht23, u2ehi0, u3elo0]
                    · linarith only [h118, h119, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h117, h118, hc24, hlam, hphi, u2ehi2]
                · linarith only [h117, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                    · linarith only [h1, h112, h115, h126, hlam, hphi, ht23, u2ehi0, u3elo0]
                    · linarith only [h125, h126, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h124, h125, hc24, hlam, hphi, u2ehi2]
                · linarith only [h124, hlam, hphi, ht23, u2ehi1, u3elo2]
            · linarith only [h114, h115, h2, hlam, hphi, ht23, u2ehi0, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h132 | h132
            · linarith only [h114, h132, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
              · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                · linarith only [h0, h114, h135, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h135, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                · linarith only [h0, h114, h138, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h138, hlam, hphi, ht23, u2ehi1, u3elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h141 | h141
      · rcases m.htr 0 2 5 (by decide) (by decide) with h142 | h142
        · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
          · rcases m.htr 0 3 5 (by decide) (by decide) with h144 | h144
            · linarith only [h0, h1, h144, hlam]
            · linarith only [h141, h143, h144, hlam, hphi, ht23, u2ehi3, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h147 | h147
            · linarith only [h143, h147, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                · linarith only [h0, h1, h143, h149, h150, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h150, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                · linarith only [h0, h143, h153, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h153, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h141, h142, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
        · linarith only [h141, h157, hc24, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 3 5 (by decide) (by decide) with h160 | h160
            · linarith only [h0, h1, h160, hlam]
            · linarith only [h141, h159, h160, hlam, hphi, ht23, u2ehi0, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
            · linarith only [h159, h163, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                · linarith only [h0, h159, h166, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h166, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                · linarith only [h0, h159, h169, hlam, hphi, ht23, u2ehi2, u3elo3]
                · linarith only [h169, hlam, hphi, ht23, u2ehi1, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
    · linarith only [h0, h172, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
      · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
        · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
          · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
            · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
              · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                                  · linarith only [h176, h188, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                                  · rcases h5bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h172, hlam, p190_1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h172, h182, h184, hlam, hphi, ht23, p190_1, u2ehi4, u3elo1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h172, h182, h184, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p190_1, u3elo1, u5ehi3]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h172, h182, h184, h188, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p190_1, u3elo1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h182, h184, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p190_1, u3elo1, u5ehi0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h182, h184, hlam, hphi, ht23, p190_1, u2ehi4, u3elo1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h182, h184, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p190_1, u3elo1, u5ehi3]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h182, h184, h188, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p190_1, u3elo1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h175, hlam, p190_1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h181, hlam, p190_1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h172, h175, h182, h184, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p190_1, u3elo1, u5ehi3]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h174, h187, h188, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p190_1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h177, hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h183, hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h186, hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h188, hlam, p190_1]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h178, hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h184, hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h187, hlam, p190_0]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [h0, h176, h178, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p190_1, u3elo1, u5ehi3]
                                    · have p190_0 := h190c.1
                                      have p190_1 := h190c.2.1
                                      have p190_2 := h190c.2.2.1
                                      have p190_3 := h190c.2.2.2
                                      linarith only [hlam, p190_0]
                                · linarith only [h0, h176, h178, h187, hlam, hphi, ht23, u2ehi3, u3elo1]
                              · linarith only [h186, hlam, hphi, ht23, u2ehi2, u3elo4]
                            · linarith only [h185, hlam, hphi, ht23, u2ehi2, u3elo3]
                          · linarith only [h0, h176, h178, h180, h184, hlam, hphi, ht23, u2ehi3, u3elo1]
                        · linarith only [h0, h177, h183, hlam]
                      · linarith only [h0, h176, h182, hlam]
                    · linarith only [h179, h181, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h179, h180, hc24, hlam, hphi, u2ehi2]
                · linarith only [h179, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
                · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
                          · linarith only [h174, h178, h228, h230, hlam, hphi, ht23, u2ehi3, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                                · linarith only [h174, h178, h234, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                                  · linarith only [h178, h225, h232, h236, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h5bigk with h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h172, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h0, h177, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p238_1, u3elo1, u5ehi2]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h0, h177, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p238_1, u3elo1, u5ehi3]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h178, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h229, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p238_1, u3elo1, u5ehi0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h229, hlam, hphi, ht23, p238_1, u2ehi4, u3elo1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h229, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p238_1, u3elo1, u5ehi3]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h230, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h175, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h227, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h175, hc02, hlam, hphi, ht0b, ht5b, p238_1, u5ehi3]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h234, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h177, hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h229, hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h233, hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [hlam, p238_0]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h236, hlam, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h175, hc45, hlam, hphi, ht23, ht34, p238_1, u2ehi4]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [h172, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p238_1]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht23, ht34, p238_1, u2ehi4]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      rcases p238_3 (m.d 0 5) (by simp) with h262 | h262
                                      · linarith only [h178, h262, hlam]
                                      · linarith only [h177, h262, hlam]
                                    · have p238_0 := h238c.1
                                      have p238_1 := h238c.2.1
                                      have p238_2 := h238c.2.2.1
                                      have p238_3 := h238c.2.2.2
                                      linarith only [hlam, p238_0]
                              · linarith only [h233, hlam, hphi, ht23, u2ehi2, u3elo4]
                            · linarith only [h232, hlam, hphi, ht23, u2ehi2, u3elo3]
                        · linarith only [h0, h177, h229, hlam]
                      · linarith only [h0, h176, h228, hlam]
                    · linarith only [h0, h175, h177, h227, hlam, hphi, ht23, u2ehi1, u3elo1]
                  · linarith only [h225, h226, hc24, hlam, hphi, u2ehi2]
                · linarith only [h225, hlam, hphi, ht23, u2ehi1, u3elo2]
            · linarith only [h174, h176, h177, hlam, hphi, ht23, u2ehi3, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h274 | h274
            · linarith only [h176, h274, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
              · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
                      · linarith only [h176, h280, hc03, hlam, hphi, u3elo1]
                      · linarith only [h277, h280, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h277, h279, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h277, h278, hc24, hlam, hphi, u2ehi2]
                · linarith only [h277, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                      · linarith only [h0, h176, h289, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h286, h289, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h287, h288, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h286, h287, hc24, hlam, hphi, u2ehi2]
                · linarith only [h286, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h174, h175, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h296 | h296
        · linarith only [h174, h296, hc24, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h298 | h298
          · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
            · rcases m.htr 0 4 5 (by decide) (by decide) with h300 | h300
              · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                      · linarith only [h174, h302, h304, hlam, hphi, ht23, u2ehi0, u3elo1]
                      · linarith only [h0, h298, h300, h304, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                    · linarith only [h301, h303, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h301, h302, hc24, hlam, hphi, u2ehi2]
                · linarith only [h301, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
                · rcases m.htr 1 2 4 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h312 | h312
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h313 | h313
                      · linarith only [h174, h311, h313, hlam, hphi, ht23, u2ehi0, u3elo1]
                      · linarith only [h310, h313, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h310, h312, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h310, h311, hc24, hlam, hphi, u2ehi2]
                · linarith only [h310, hlam, hphi, ht23, u2ehi1, u3elo2]
            · linarith only [h174, h298, h299, hlam, hphi, ht23, u2ehi0, u3elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
            · linarith only [h298, h320, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h322 | h322
              · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                · rcases m.htr 1 2 4 (by decide) (by decide) with h324 | h324
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                      · linarith only [h298, h326, hc03, hlam, hphi, u3elo1]
                      · linarith only [h323, h326, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h324, h325, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h323, h324, hc24, hlam, hphi, u2ehi2]
                · linarith only [h323, hlam, hphi, ht23, u2ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                      · linarith only [h0, h298, h335, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h332, h335, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h333, h334, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h332, h333, hc24, hlam, hphi, u2ehi2]
                · linarith only [h332, hlam, hphi, ht23, u2ehi1, u3elo2]

end R2N4
