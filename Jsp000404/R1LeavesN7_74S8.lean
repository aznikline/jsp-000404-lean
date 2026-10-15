import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_24_L_0_M_LI (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
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
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h11, h13, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h13, h6, hc34, hlam, hphi, u4elo0]
                          · linarith only [h10, h12, h2, hc24, hlam, hphi, u4elo0]
                        · linarith only [h11, h5, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h6, hc14, hlam, hphi, u4elo0]
                    · linarith only [h5, h9, hc13, hlam, hphi, u3elo0]
                  · linarith only [h4, h7, h8, hc23, hlam, hphi, ht34, u4elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                          · linarith only [h21, h25, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h23, h25, hc24, hlam, hphi, u4elo1]
                        · linarith only [h24, h7, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h23, h6, hc14, hlam, hphi, u4elo0]
                    · linarith only [h21, h22, h7, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                            · rcases h4bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h31, h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p36_1, u4elo0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h21, hc12, hlam, hphi, ht23, ht34, p36_1, u4elo0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p36_1, u4elo0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                rcases p36_3 (m.d 0 4) (by simp) with h41 | h41
                                · rcases p36_3 (m.d 1 4) (by simp) with h42 | h42
                                  · linarith only [h2, h42, hlam]
                                  · linarith only [h32, h42, hlam]
                                · linarith only [h41, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h2, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h21, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p36_1, u4elo1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                rcases p36_3 (m.d 0 4) (by simp) with h50 | h50
                                · rcases p36_3 (m.d 1 4) (by simp) with h51 | h51
                                  · rcases p36_3 (m.d 2 4) (by simp) with h52 | h52
                                    · rcases p36_3 (m.d 3 4) (by simp) with h53 | h53
                                      · linarith only [h31, h53, hlam]
                                      · linarith only [h35, h53, hlam]
                                    · linarith only [h34, h52, hlam]
                                  · linarith only [h51, hlam, p36_0]
                                · linarith only [h50, h6, hlam]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h4, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hc14, hlam, hphi, p36_1, u4elo2]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h35, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p36_1, u4elo0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                rcases p36_3 (m.d 0 4) (by simp) with h63 | h63
                                · rcases p36_3 (m.d 1 4) (by simp) with h64 | h64
                                  · linarith only [h21, h64, hlam]
                                  · linarith only [h32, h64, hlam]
                                · linarith only [h6, h63, hlam]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h5, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h31, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h33, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h31, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p36_1, u3elo1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h6, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h32, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h34, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h35, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                            · linarith only [h35, h6, hc34, hlam, hphi, u4elo0]
                          · linarith only [h21, h34, h6, hc14, hlam, hphi, u4elo0]
                        · linarith only [h33, h5, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h32, h6, hc14, hlam, hphi, u4elo0]
                    · linarith only [h31, h5, h7, hc12, hlam, hphi, ht23, u3elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h6, h86, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h6, h89, hc04, hlam, hphi, u4elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                            · linarith only [h2, h6, h84, h88, h91, hlam]
                            · rcases h4bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h6, h84, h88, hc34, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h6, h88, hc34, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h6, hc34, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h6, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h2, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h88, hc34, hlam, hphi, p93_1, u4elo1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h2, h6, hc34, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h86, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h4, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h84, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hc34, hlam, hphi, p93_1, u4elo2]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h89, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h5, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h85, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h88, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h91, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hc04, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h84, hc24, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h88, hc34, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hc34, hlam, hphi, p93_1, u4elo4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                        · linarith only [h5, h88, hc23, hlam, hphi, u3elo0]
                    · linarith only [h5, h6, h83, h85, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h83, h84, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                      · linarith only [h124, h6, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                          · linarith only [h122, h127, h2, h6, h83, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                            · linarith only [h122, h126, h129, h2, h6, hlam]
                            · rcases h4bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h6, hc14, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h126, h6, hc34, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h6, hc34, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h6, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h2, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h126, hc34, hlam, hphi, p131_1, u4elo1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h2, h6, hc34, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h124, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h4, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h122, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h122, h3, h83, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p131_1, u3elo0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h127, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h5, hlam, p131_1]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h123, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h126, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h129, hlam, p131_0]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hc04, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h122, hc24, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [h126, hc34, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hc34, hlam, hphi, p131_1, u4elo4]
                              · have p131_0 := h131c.1
                                have p131_1 := h131c.2.1
                                have p131_2 := h131c.2.2.1
                                have p131_3 := h131c.2.2.2
                                linarith only [hlam, p131_0]
                        · linarith only [h126, h83, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h123, h5, hc13, hlam, hphi, u3elo0]
                  · linarith only [h122, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
              · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                    · linarith only [h1, h163, h5, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                        · linarith only [h1, h161, h166, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h168 | h168
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h169 | h169
                            · rcases h4bigk with h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h163, hc13, hlam, hphi, ht34, p170_1, u4elo0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h168, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p170_1, u4elo0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h5, hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                rcases p170_3 (m.d 0 4) (by simp) with h175 | h175
                                · rcases p170_3 (m.d 1 4) (by simp) with h176 | h176
                                  · linarith only [h176, h2, hlam]
                                  · linarith only [h165, h176, hlam]
                                · linarith only [h175, hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h2, hlam, p170_1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h168, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p170_1, u4elo1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h163, hlam, p170_1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                rcases p170_3 (m.d 0 4) (by simp) with h184 | h184
                                · rcases p170_3 (m.d 1 4) (by simp) with h185 | h185
                                  · rcases p170_3 (m.d 2 4) (by simp) with h186 | h186
                                    · linarith only [h162, h186, hlam]
                                    · linarith only [h168, h186, hlam]
                                  · linarith only [h185, hlam, p170_0]
                                · linarith only [h160, h184, hlam]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h4, hlam, p170_1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h162, hlam, p170_1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h166, hlam, p170_1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h0, h162, hc01, hc45, hlam, hphi, ht0b, ht5b, p170_1]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h2, hc14, hlam, hphi, p170_1, u4elo3]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hc14, hlam, hphi, p170_1, u4elo3]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hc24, hlam, hphi, p170_1, u4elo3]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                rcases p170_3 (m.d 0 4) (by simp) with h200 | h200
                                · linarith only [h200, h5, hlam]
                                · linarith only [h160, h200, hlam]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h160, hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h165, hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h168, hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [h169, hlam, p170_0]
                              · have p170_0 := h170c.1
                                have p170_1 := h170c.2.1
                                have p170_2 := h170c.2.2.1
                                have p170_3 := h170c.2.2.2
                                linarith only [hlam, p170_0]
                            · linarith only [h162, h168, h169, h2, hc34, hlam, hphi, u4elo0]
                          · linarith only [h160, h168, hc24, hlam, hphi, u4elo0]
                      · linarith only [h160, h165, h5, hc14, hlam, hphi, u4elo3]
                  · linarith only [h161, h162, h4, h5, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h161, h3, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                    · linarith only [h1, h160, h215, h5, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                      · linarith only [h160, h217, h5, hc03, hlam, hphi, ht34, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                        · linarith only [h1, h213, h219, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h221 | h221
                          · linarith only [h1, h160, h213, h221, h5, hc23, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h223 | h223
                            · linarith only [h1, h160, h213, h223, h5, hc23, hlam, hphi, u3elo3]
                            · linarith only [h1, h213, h223, h5, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h160, h214, h4, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h213, h3, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
          · rcases m.htr 0 3 4 (by decide) (by decide) with h230 | h230
            · rcases m.htr 0 4 5 (by decide) (by decide) with h231 | h231
              · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                · linarith only [h0, h229, h232, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                          · linarith only [h0, h234, h238, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h2, h236, h238, hc24, hlam, hphi, u4elo0]
                        · linarith only [h237, h3, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h229, h231, h236, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h232, h234, h235, hc24, hlam, hphi, u4elo3]
                  · linarith only [h229, h234, h3, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
                · linarith only [h0, h229, h245, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h249 | h249
                      · linarith only [h231, h249, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                          · linarith only [h2, h231, h247, h252, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h254 | h254
                            · linarith only [h2, h231, h247, h251, h254, hlam]
                            · rcases h4bigk with h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h231, h247, h251, hc34, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h231, h251, hc34, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h231, hc34, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h231, hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h2, hlam, p256_1]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h251, hc34, hlam, hphi, p256_1, u4elo1]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h2, h231, hc34, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h249, hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h229, hlam, p256_1]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h247, hlam, p256_1]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h0, h247, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p256_1, u3elo2]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h252, hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h230, hlam, p256_1]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h248, hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h251, hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h254, hlam, p256_0]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hc04, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h247, hc24, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [h251, hc34, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hc34, hlam, hphi, p256_1, u4elo4]
                              · have p256_0 := h256c.1
                                have p256_1 := h256c.2.1
                                have p256_2 := h256c.2.2.1
                                have p256_3 := h256c.2.2.2
                                linarith only [hlam, p256_0]
                        · linarith only [h251, h3, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h230, h245, h247, h248, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h229, h247, h3, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h229, h230, h3, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h286 | h286
            · rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
              · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
                · linarith only [h0, h229, h288, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
                  · linarith only [h229, h288, h290, hc02, hlam, hphi, ht23, u3elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
                            · rcases h4bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h292, h296, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p297_1, u4elo0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h229, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h296, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p297_1, u4elo0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                rcases p297_3 (m.d 0 4) (by simp) with h302 | h302
                                · rcases p297_3 (m.d 1 4) (by simp) with h303 | h303
                                  · linarith only [h2, h303, hlam]
                                  · linarith only [h293, h303, hlam]
                                · linarith only [h302, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h2, hlam, p297_1]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h290, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h296, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p297_1, u4elo1]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                rcases p297_3 (m.d 0 4) (by simp) with h311 | h311
                                · rcases p297_3 (m.d 1 4) (by simp) with h312 | h312
                                  · rcases p297_3 (m.d 2 4) (by simp) with h313 | h313
                                    · rcases p297_3 (m.d 3 4) (by simp) with h314 | h314
                                      · linarith only [h292, h314, hlam]
                                      · linarith only [h296, h314, hlam]
                                    · linarith only [h295, h313, hlam]
                                  · linarith only [h312, hlam, p297_0]
                                · linarith only [h287, h311, hlam]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hc04, hlam, hphi, p297_1, u4elo2]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hc14, hlam, hphi, p297_1, u4elo2]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h296, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p297_1, u4elo2]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                rcases p297_3 (m.d 0 4) (by simp) with h324 | h324
                                · linarith only [h229, h324, hlam]
                                · linarith only [h287, h324, hlam]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h286, hlam, p297_1]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h292, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h294, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h1, h292, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p297_1, u3elo0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h287, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h293, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h295, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [h296, hlam, p297_0]
                              · have p297_0 := h297c.1
                                have p297_1 := h297c.2.1
                                have p297_2 := h297c.2.2.1
                                have p297_3 := h297c.2.2.2
                                linarith only [hlam, p297_0]
                            · linarith only [h287, h296, hc34, hlam, hphi, u4elo0]
                          · linarith only [h0, h229, h295, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h294, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h287, h293, hc14, hlam, hphi, u4elo0]
                    · linarith only [h286, h292, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
                · linarith only [h0, h229, h287, h3, h342, hc03, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                  · linarith only [h0, h229, h287, h344, hc24, hlam, hphi, u4elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                      · linarith only [h2, h287, h347, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
                          · linarith only [h229, h287, h349, h350, hc02, hlam, hphi, ht23, u3elo2]
                          · linarith only [h0, h229, h350, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h1, h346, h349, hc23, hlam, hphi, u3elo0]
                    · linarith only [h286, h3, h346, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h355 | h355
              · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
                · linarith only [h0, h229, h356, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                  · linarith only [h0, h286, h3, h358, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                    · linarith only [h1, h286, h360, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                        · linarith only [h286, h3, h363, hc02, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h3, h363, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h355, h362, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                · linarith only [h0, h3, h367, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
                  · linarith only [h0, h229, h369, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                    · linarith only [h1, h286, h355, h371, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h373 | h373
                      · linarith only [h286, h3, h355, h373, hc02, hlam, hphi, ht23, ht34, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h286, h3, h375, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h3, h375, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h380 | h380
    · rcases m.htr 0 1 4 (by decide) (by decide) with h381 | h381
      · rcases m.htr 0 2 3 (by decide) (by decide) with h382 | h382
        · rcases m.htr 0 2 4 (by decide) (by decide) with h383 | h383
          · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
            · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
              · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                · rcases m.htr 1 2 4 (by decide) (by decide) with h387 | h387
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h390 | h390
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h392 | h392
                            · linarith only [h0, h380, h386, h390, h392, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h385, h392, hc34, hlam, hphi, u4elo0]
                          · linarith only [h0, h380, h388, h389, h391, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h384, h390, hc23, hlam, hphi, u3elo0]
                      · linarith only [h385, h389, hc14, hlam, hphi, u4elo0]
                    · linarith only [h384, h388, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h387, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h380, h386, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h404 | h404
                      · linarith only [h385, h404, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h407 | h407
                          · linarith only [h381, h385, h402, h407, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                            · linarith only [h380, h385, h401, h406, h409, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
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
                                linarith only [h385, h402, h406, hc34, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h385, h406, hc34, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h385, hc34, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h385, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h381, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h406, hc34, hlam, hphi, p411_1, u4elo1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h381, h385, hc34, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h404, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h383, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h402, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hc34, hlam, hphi, p411_1, u4elo2]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h407, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h384, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h403, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h406, hlam, p411_0]
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
                                linarith only [hc04, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h402, hc24, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h406, hc34, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hc34, hlam, hphi, p411_1, u4elo4]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                        · linarith only [h384, h406, hc23, hlam, hphi, u3elo0]
                    · linarith only [h384, h385, h403, hc13, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h402, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h380, h401, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h441 | h441
              · rcases m.htr 1 2 3 (by decide) (by decide) with h442 | h442
                · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                    · linarith only [h0, h380, h384, h444, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                        · linarith only [h380, h384, h442, h447, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                            · rcases h4bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h384, hc14, hlam, hphi, p451_1, u4elo3]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h384, h449, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p451_1, u4elo3]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h384, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                rcases p451_3 (m.d 0 4) (by simp) with h456 | h456
                                · rcases p451_3 (m.d 1 4) (by simp) with h457 | h457
                                  · linarith only [h381, h457, hlam]
                                  · linarith only [h446, h457, hlam]
                                · linarith only [h456, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h381, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h449, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p451_1, u4elo1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h444, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h0, h381, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h383, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h443, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h447, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h0, h381, h443, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hc04, hlam, hphi, p451_1, u4elo3]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hc14, hlam, hphi, p451_1, u4elo3]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hc24, hlam, hphi, p451_1, u4elo3]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                rcases p451_3 (m.d 0 4) (by simp) with h475 | h475
                                · linarith only [h384, h475, hlam]
                                · linarith only [h441, h475, hlam]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h441, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h446, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h449, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h450, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                            · linarith only [h384, h450, hc03, hlam, hphi, ht34, u4elo4]
                          · linarith only [h381, h446, h449, hc24, hlam, hphi, u4elo0]
                      · linarith only [h384, h441, h446, hc14, hlam, hphi, u4elo3]
                  · linarith only [h0, h443, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h380, h442, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                · rcases m.htr 1 2 4 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
                    · linarith only [h380, h384, h441, h490, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                      · linarith only [h0, h381, h384, h441, h492, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
                        · linarith only [h380, h384, h488, h494, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h496 | h496
                          · linarith only [h381, h441, h489, h496, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h498 | h498
                            · linarith only [h441, h498, hc04, hlam, hphi, u4elo3]
                            · linarith only [h380, h384, h488, h498, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h489, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h380, h488, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h380, h383, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h380, h382, hc13, hlam, hphi, u3elo2]
      · linarith only [h380, h381, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h506 | h506
      · rcases m.htr 0 2 3 (by decide) (by decide) with h507 | h507
        · rcases m.htr 0 2 4 (by decide) (by decide) with h508 | h508
          · rcases m.htr 0 3 4 (by decide) (by decide) with h509 | h509
            · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
              · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
                · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h514 | h514
                      · linarith only [h380, h506, h514, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h510, h514, hc14, hlam, hphi, u4elo0]
                    · linarith only [h380, h506, h512, h513, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h380, h506, h511, h512, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h506, h507, h511, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h520 | h520
                · rcases m.htr 1 2 4 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                      · linarith only [h380, h506, h510, h523, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h525 | h525
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h526 | h526
                          · linarith only [h506, h510, h521, h526, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h528 | h528
                            · linarith only [h506, h510, h521, h525, h528, hlam]
                            · rcases h4bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h510, hc14, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h510, h525, hc34, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h510, hc34, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h510, hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h506, hlam, p530_1]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h380, h506, h525, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p530_1, u3elo1]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h380, h506, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p530_1, u3elo1]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h523, hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h508, hlam, p530_1]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h521, hlam, p530_1]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hc34, hlam, hphi, p530_1, u4elo2]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h526, hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h509, hlam, p530_1]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h522, hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h525, hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h528, hlam, p530_0]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hc04, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h521, hc24, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [h525, hc34, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hc34, hlam, hphi, p530_1, u4elo4]
                              · have p530_0 := h530c.1
                                have p530_1 := h530c.2.1
                                have p530_2 := h530c.2.2.1
                                have p530_3 := h530c.2.2.2
                                linarith only [hlam, p530_0]
                        · linarith only [h380, h509, h525, hc23, hlam, hphi, u3elo1]
                    · linarith only [h380, h522, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h380, h506, h508, h521, hc02, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h520, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h380, h506, h509, hc14, hlam, hphi, u4elo3]
          · linarith only [h507, h508, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h562 | h562
          · rcases m.htr 0 3 4 (by decide) (by decide) with h563 | h563
            · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
              · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h568 | h568
                      · linarith only [h0, h506, h507, h565, h568, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h0, h506, h507, h564, h565, h566, h568, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h0, h507, h565, h567, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h507, h562, h565, h566, hlam]
                · linarith only [h0, h506, h565, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                      · linarith only [h0, h506, h507, h564, h577, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
                          · linarith only [h564, h580, hc04, hlam, hphi, u4elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                            · linarith only [h506, h564, h575, h579, h582, hlam]
                            · rcases h4bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h564, h575, h579, hc34, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h564, h579, hc34, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h564, hc34, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h564, hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h506, hlam, p584_1]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h0, h506, h507, h574, h579, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p584_1, u3elo1]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h0, h506, h507, h574, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p584_1, u3elo1]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h577, hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h562, hlam, p584_1]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h575, hlam, p584_1]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hc34, hlam, hphi, p584_1, u4elo2]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h580, hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h563, hlam, p584_1]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h576, hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h579, hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h582, hlam, p584_0]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hc04, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h575, hc24, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [h579, hc34, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hc34, hlam, hphi, p584_1, u4elo4]
                              · have p584_0 := h584c.1
                                have p584_1 := h584c.2.1
                                have p584_2 := h584c.2.2.1
                                have p584_3 := h584c.2.2.2
                                linarith only [hlam, p584_0]
                        · linarith only [h0, h507, h579, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h506, h507, h563, h564, h574, h575, h576, hc24, hlam, hphi, u4elo4]
                  · linarith only [h0, h507, h574, h575, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h506, h574, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h380, h506, h563, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h506, h562, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h616 | h616
        · rcases m.htr 0 2 4 (by decide) (by decide) with h617 | h617
          · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
            · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
              · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h625 | h625
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h626 | h626
                            · rcases h4bigk with h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h506, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hc24, hlam, hphi, p627_1, u4elo0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h506, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p627_1, u4elo1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                rcases p627_3 (m.d 0 4) (by simp) with h632 | h632
                                · rcases p627_3 (m.d 1 4) (by simp) with h633 | h633
                                  · rcases p627_3 (m.d 2 4) (by simp) with h634 | h634
                                    · linarith only [h617, h634, hlam]
                                    · linarith only [h625, h634, hlam]
                                  · linarith only [h623, h633, hlam]
                                · linarith only [h632, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hc04, hlam, hphi, p627_1, u4elo1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h624, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p627_1, u4elo1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p627_1, u4elo1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                rcases p627_3 (m.d 0 4) (by simp) with h643 | h643
                                · linarith only [h506, h643, hlam]
                                · linarith only [h619, h643, hlam]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h617, hlam, p627_1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h621, hlam, p627_1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h617, h626, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p627_1, u4elo0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                rcases p627_3 (m.d 0 4) (by simp) with h650 | h650
                                · rcases p627_3 (m.d 1 4) (by simp) with h651 | h651
                                  · rcases p627_3 (m.d 2 4) (by simp) with h652 | h652
                                    · rcases p627_3 (m.d 3 4) (by simp) with h653 | h653
                                      · linarith only [h624, h653, hlam]
                                      · linarith only [h626, h653, hlam]
                                    · linarith only [h652, hlam, p627_0]
                                  · linarith only [h623, h651, hlam]
                                · linarith only [h619, h650, hlam]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h618, hlam, p627_1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h622, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h624, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h618, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p627_1, u3elo0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h619, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h623, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h625, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h626, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                            · linarith only [h506, h619, h626, hc34, hlam, hphi, u4elo1]
                          · linarith only [h506, h619, h625, hc24, hlam, hphi, u4elo1]
                        · linarith only [h618, h624, hc23, hlam, hphi, u3elo0]
                      · linarith only [h506, h619, h623, hlam]
                    · linarith only [h380, h618, h622, hlam]
                  · linarith only [h0, h621, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h620, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
                · rcases m.htr 1 2 4 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h679 | h679
                      · linarith only [h619, h679, hc04, hlam, hphi, u4elo1]
                      · linarith only [h506, h679, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h380, h678, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h616, h617, h677, hc23, hlam, hphi, ht34, u4elo0]
                · linarith only [h0, h676, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h685 | h685
              · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
                · rcases m.htr 1 2 4 (by decide) (by decide) with h687 | h687
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h688 | h688
                    · linarith only [h618, h688, hc03, hlam, hphi, u3elo1]
                    · linarith only [h380, h688, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h380, h686, h687, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h686, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h693 | h693
                · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h695 | h695
                    · linarith only [h618, h695, hc03, hlam, hphi, u3elo1]
                    · linarith only [h380, h695, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h380, h693, h694, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h693, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h616, h617, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h701 | h701
          · rcases m.htr 0 3 4 (by decide) (by decide) with h702 | h702
            · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
              · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h706 | h706
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h707 | h707
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h708 | h708
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h709 | h709
                          · linarith only [h616, h701, h704, h709, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h703, h708, h709, hc34, hlam, hphi, u4elo0]
                        · linarith only [h616, h701, h708, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h616, h701, h703, h704, h707, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h616, h701, h702, h704, h706, hlam]
                  · linarith only [h616, h701, h704, h705, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h704, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
                · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h719 | h719
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h720 | h720
                      · linarith only [h703, h720, hc04, hlam, hphi, u4elo1]
                      · linarith only [h506, h616, h701, h717, h720, hc01, hc24, hlam, hphi, ht12, ht23, u3elo1, u4elo4]
                    · linarith only [h616, h701, h717, h719, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h616, h701, h717, h718, hlam]
                · linarith only [h0, h717, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h616, h701, h702, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 0 4 5 (by decide) (by decide) with h728 | h728
              · rcases m.htr 1 2 3 (by decide) (by decide) with h729 | h729
                · rcases m.htr 1 2 4 (by decide) (by decide) with h730 | h730
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h732 | h732
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h733 | h733
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h734 | h734
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h735 | h735
                            · rcases h4bigk with h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h506, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h701, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h735, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p736_1, u4elo0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                rcases p736_3 (m.d 0 4) (by simp) with h741 | h741
                                · rcases p736_3 (m.d 1 4) (by simp) with h742 | h742
                                  · rcases p736_3 (m.d 2 4) (by simp) with h743 | h743
                                    · rcases p736_3 (m.d 3 4) (by simp) with h744 | h744
                                      · linarith only [h727, h744, hlam]
                                      · linarith only [h735, h744, hlam]
                                    · linarith only [h734, h743, hlam]
                                  · linarith only [h732, h742, hlam]
                                · linarith only [h741, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [hc04, hlam, hphi, p736_1, u4elo1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h0, h701, hc01, hlam, hphi, ht12, ht23, ht34, p736_1, u4elo1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h735, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p736_1, u4elo1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                rcases p736_3 (m.d 0 4) (by simp) with h754 | h754
                                · linarith only [h506, h754, hlam]
                                · linarith only [h728, h754, hlam]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h727, h735, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p736_1, u4elo2]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h730, hlam, p736_1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h730, h735, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p736_1, u4elo1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                rcases p736_3 (m.d 0 4) (by simp) with h761 | h761
                                · linarith only [h701, h761, hlam]
                                · linarith only [h728, h761, hlam]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h727, hlam, p736_1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h731, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h733, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h616, h727, h729, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p736_1, u3elo1]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h728, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h732, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h734, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [h735, hlam, p736_0]
                              · have p736_0 := h736c.1
                                have p736_1 := h736c.2.1
                                have p736_2 := h736c.2.2.1
                                have p736_3 := h736c.2.2.2
                                linarith only [hlam, p736_0]
                            · linarith only [h701, h728, h730, h735, hc34, hlam, hphi, u4elo1]
                          · linarith only [h701, h728, h734, hlam]
                        · linarith only [h0, h616, h733, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h728, h732, hc14, hlam, hphi, u4elo0]
                    · linarith only [h727, h731, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h730, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h729, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h781 | h781
                · rcases m.htr 1 2 4 (by decide) (by decide) with h782 | h782
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h784 | h784
                      · linarith only [h728, h784, hc04, hlam, hphi, u4elo1]
                      · linarith only [h506, h784, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h380, h783, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h616, h781, h782, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h781, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h790 | h790
              · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
                    · linarith only [h0, h616, h727, h793, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h380, h793, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h616, h791, h792, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h791, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                · rcases m.htr 1 2 4 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h800 | h800
                    · linarith only [h0, h616, h727, h800, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h380, h800, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h616, h798, h799, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h798, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
