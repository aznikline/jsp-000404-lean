import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3960000 in
theorem n7l_sAA2_H_I_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                    · linarith only [h0, h15, h17, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h15, h16, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h12, h14, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                                  · linarith only [h0, h14, h22, h23, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                                    · linarith only [h0, h14, h22, h25, h9, hc01, hc15, hlam, hphi, ht0b, ht5b]
                                    · rcases h0bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h3, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h14, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h1, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h4, hlam, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h14, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h2, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h5, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h22, h4, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h14, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h3, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h6, hlam, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h7, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h8, hlam, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                · linarith only [h1, h12, h22, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                              · linarith only [h12, h13, h54, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                  · linarith only [h0, h54, h56, h57, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                                    · linarith only [h0, h10, h13, h4, h54, h56, h59, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h4, hlam, p61_1]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h10, h12, h13, h59, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h10, h12, h13, h4, h59, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h2, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h5, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, h10, h12, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h10, h12, h13, h5, h59, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h3, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h6, hlam, p61_1]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h7, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h8, hlam, p61_1]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                · linarith only [h12, h13, h56, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                                · linarith only [h11, h12, h88, h90, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                                    · rcases h0bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, h11, h88, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h5, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi2]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h11, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, h11, h88, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h5, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi2]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h11, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h4, hlam, p94_1]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h11, h12, h2, h88, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h11, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h2, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h5, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, h11, h88, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h11, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h3, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h6, hlam, p94_1]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h7, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h8, hlam, p94_1]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                    · linarith only [h11, h12, h88, h92, h93, hc24, hlam, hphi, u2ehi4]
                                  · linarith only [h2, h89, h92, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h12, h88, h89, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                                · linarith only [h0, h12, h124, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                                    · rcases h0bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h124, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h88, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h124, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h1, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h4, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h8, h88, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h4, h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h2, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h5, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h1, h9, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h5, h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h3, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h6, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h8, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                    · linarith only [h0, h10, h126, h127, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h10, h123, h126, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                                · linarith only [h12, h156, h9, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                                  · linarith only [h10, h123, h158, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                                    · linarith only [h12, h123, h160, h9, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h12, h160, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h11, h9, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
                      · linarith only [h165, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                        · linarith only [h0, h167, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                                    · rcases h0bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h172, h173, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h171, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h172, h173, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h171, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h1, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h4, hlam, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h173, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h2, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h5, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h1, h169, h174, hc04, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h3, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h6, hlam, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h7, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h8, hlam, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                    · rcases h0bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h165, h171, h172, h174, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h171, h174, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h165, h171, h172, h174, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h171, h174, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h1, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h4, hlam, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h167, h6, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h167, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h2, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h5, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h1, h169, h171, h174, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h167, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h3, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h6, hlam, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h7, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h8, hlam, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                  · linarith only [h1, h169, h171, h173, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h172, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                                  · linarith only [h165, h171, h229, h230, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h165, h230, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h229, h9, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                              · linarith only [h169, h170, h234, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                                  · linarith only [h0, h165, h234, h236, h237, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h165, h237, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h169, h170, h236, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h241 | h241
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                                · linarith only [h0, h169, h241, h243, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h243, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h169, h241, h242, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                                · linarith only [h0, h169, h248, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h248, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                                · linarith only [h169, h251, h9, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h251, h9, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                              · linarith only [h2, h259, h8, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                                  · linarith only [h0, h254, h261, h262, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                                    · linarith only [h0, h2, h254, h255, h261, h264, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h1, h254, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi2]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h255, h259, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h0, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h1, h254, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi2]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h0, h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h0, h255, h259, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h1, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h4, hlam, p266_1]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, h255, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h255, h259, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h5, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h8, hc03, hc45, hlam, hphi, ht34, p266_1]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h8, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h3, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h6, hlam, p266_1]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h7, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, h255, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                · linarith only [h1, h257, h261, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                              · linarith only [h257, h258, h293, h3, h8, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                                  · linarith only [h255, h257, h258, h296, h7, h8, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h298 | h298
                                    · linarith only [h255, h257, h258, h295, h298, h7, h8, hc23, hlam, hphi, u2ehi3]
                                    · rcases h0bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, h255, h257, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h255, h257, h258, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, h255, h257, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h255, h257, h258, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h4, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, h255, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h255, h257, h258, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h5, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, h255, h257, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h8, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h3, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h6, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h7, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h8, hc04, hc45, hlam, hphi, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                · linarith only [h257, h258, h295, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                              · linarith only [h2, h328, h8, hlam]
                              · linarith only [h257, h327, h328, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                              · linarith only [h2, h331, h8, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                                · linarith only [h0, h254, h257, h333, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                                  · linarith only [h2, h254, h257, h335, h8, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                                    · linarith only [h2, h254, h257, h337, h8, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h254, h257, h337, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h254, h256, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h254, h255, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h254, h342, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h342, h5, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h350 | h350
                            · linarith only [h1, h350, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                              · linarith only [h349, h350, h352, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                  · linarith only [h347, h352, h355, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h357 | h357
                                    · linarith only [h0, h346, h347, h352, h354, h357, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · linarith only [h345, h357, h7, hlam]
                                · linarith only [h1, h349, h354, h7, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                            · linarith only [h1, h361, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                                · linarith only [h349, h364, h4, h7, hc13, hc35, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                                    · rcases h0bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h364, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h0, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h0, h364, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h0, h1, h346, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h4, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h345, h7, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h7, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h2, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h5, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, h7, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h3, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h6, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h345, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                    · linarith only [h0, h347, h366, h367, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h347, h363, h366, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                                · linarith only [h346, h349, h396, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                                  · linarith only [h0, h347, h363, h398, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h400 | h400
                                    · linarith only [h346, h349, h363, h400, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h346, h349, h400, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h346, h348, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h346, h347, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h346, h4, h7, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h408 | h408
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h410 | h410
                            · linarith only [h1, h410, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                              · linarith only [h2, h345, h412, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                                  · linarith only [h345, h415, h5, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
                                    · linarith only [h2, h345, h407, h417, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, h406, h414, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h2, h407, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, h2, h407, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, h1, h407, h409, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h4, hlam, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h2, h407, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h7, hlam, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h2, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h5, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h345, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h3, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h6, hlam, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, h417, h7, hc45, hlam, hphi, ht23, ht34, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h417, h7, hc04, hc45, hlam, hphi, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                · linarith only [h1, h409, h414, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                            · linarith only [h409, h446, h7, hc03, hc34, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                              · linarith only [h2, h345, h448, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                                · linarith only [h0, h406, h409, h450, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                                  · linarith only [h345, h452, h5, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                                    · linarith only [h2, h345, h406, h409, h454, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h406, h409, h454, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h406, h408, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h406, h407, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h4, h406, h7, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h462 | h462
            · linarith only [h4, h462, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h464 | h464
              · linarith only [h4, h464, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                    · linarith only [h0, h4, h468, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                      · linarith only [h0, h462, h470, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h0, h464, h472, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                                    · rcases h0bigk with h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h1, h474, h479, hc01, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h464, h467, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h464, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h4, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h462, hlam, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h464, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h1, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h4, h462, hc23, hlam, hphi, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h4, h464, hc23, hlam, hphi, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h2, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h1, h462, h474, h479, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h462, h464, hc24, hlam, hphi, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h3, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h466, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h467, hlam, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                    · rcases h0bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h467, h472, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h472, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h4, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h462, hlam, p506_1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h464, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h1, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, h4, h462, hc23, hlam, hphi, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h4, h472, hc23, hlam, hphi, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h2, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, h4, h462, h477, hc23, hlam, hphi, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h462, h476, h477, h479, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h466, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h467, hlam, p506_1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                  · linarith only [h1, h474, h476, h478, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h4, h477, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h462, h467, h470, h476, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h4, h466, h468, h475, hc23, hlam, hphi, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                                · linarith only [h472, h474, h536, h538, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h538, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h462, h467, h470, h537, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h4, h466, h468, h536, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
                    · linarith only [h0, h4, h543, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                      · linarith only [h0, h4, h545, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                        · linarith only [h0, h462, h467, h547, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                              · linarith only [h1, h462, h467, h549, h551, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
                                  · linarith only [h0, h462, h467, h554, hc24, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h462, h554, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h0, h4, h553, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h4, h466, h543, h550, hc23, hlam, hphi, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
                              · linarith only [h2, h467, h560, hlam]
                              · linarith only [h549, h559, h560, hlam]
                            · linarith only [h4, h466, h543, h559, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                    · linarith only [h0, h4, h565, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                      · linarith only [h0, h4, h466, h567, hc35, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                        · linarith only [h0, h4, h466, h569, hc35, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                            · linarith only [h1, h466, h572, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                              · linarith only [h571, h572, h574, hlam]
                              · linarith only [h462, h564, h567, h574, hc24, hlam, hphi, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h577 | h577
                            · linarith only [h0, h4, h466, h571, h577, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h579 | h579
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                                · linarith only [h565, h571, h580, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h580, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h462, h564, h567, h579, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                    · linarith only [h0, h4, h584, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                      · linarith only [h0, h4, h586, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h588 | h588
                        · linarith only [h0, h464, h588, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                            · linarith only [h1, h466, h591, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                              · linarith only [h3, h462, h564, h590, h591, h593, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h596 | h596
                                  · linarith only [h0, h462, h564, h595, h596, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h462, h596, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h1, h590, h595, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h600 | h600
                            · linarith only [h2, h466, h564, h590, h600, hc03, hc45, hlam, hphi, ht34]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h602 | h602
                              · linarith only [h2, h564, h602, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                                · linarith only [h584, h590, h604, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h4, h604, hc34, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h607 | h607
          · rcases m.htr 0 2 4 (by decide) (by decide) with h608 | h608
            · rcases m.htr 0 2 5 (by decide) (by decide) with h609 | h609
              · linarith only [h0, h3, h609, hlam]
              · linarith only [h607, h609, hc25, hlam, hphi, u2ehi2]
            · linarith only [h607, h608, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h613 | h613
            · linarith only [h607, h613, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h615 | h615
              · linarith only [h607, h615, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h617 | h617
                · linarith only [h1, h3, h617, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h2, h3, h619, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                    · linarith only [h0, h613, h619, h621, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                      · linarith only [h1, h3, h613, h621, h623, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                        · linarith only [h0, h607, h625, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h621, h625, hc25, hlam, hphi, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h628 | h628
        · rcases m.htr 0 2 3 (by decide) (by decide) with h629 | h629
          · rcases m.htr 0 2 4 (by decide) (by decide) with h630 | h630
            · linarith only [h0, h2, h630, hlam]
            · linarith only [h629, h630, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h633 | h633
            · linarith only [h629, h633, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h635 | h635
              · linarith only [h629, h635, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 0 4 5 (by decide) (by decide) with h638 | h638
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
                    · linarith only [h0, h629, h639, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h641 | h641
                      · linarith only [h0, h629, h641, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h0, h2, h641, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h638, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                    · linarith only [h0, h2, h646, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h648 | h648
                      · linarith only [h1, h2, h646, h648, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h646, h648, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h645, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h652 | h652
          · rcases m.htr 0 2 4 (by decide) (by decide) with h653 | h653
            · linarith only [h0, h2, h653, hlam]
            · linarith only [h652, h653, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h656 | h656
            · linarith only [h652, h656, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h658 | h658
              · linarith only [h652, h658, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h660 | h660
                · linarith only [h1, h628, h660, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                    · linarith only [h0, h2, h663, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
                      · linarith only [h1, h2, h656, h663, h665, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h2, h665, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h662, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h669 | h669
      · rcases m.htr 0 1 5 (by decide) (by decide) with h670 | h670
        · rcases m.htr 0 2 3 (by decide) (by decide) with h671 | h671
          · linarith only [h0, h1, h671, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h673 | h673
            · linarith only [h671, h673, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h675 | h675
              · linarith only [h671, h675, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h677 | h677
                · rcases m.htr 0 4 5 (by decide) (by decide) with h678 | h678
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
                    · linarith only [h0, h671, h679, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h679, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h682 | h682
                    · linarith only [h0, h1, h682, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h682, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h677, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h686 | h686
          · linarith only [h0, h1, h686, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h688 | h688
            · linarith only [h686, h688, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h690 | h690
              · linarith only [h686, h690, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h692 | h692
                · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
                  · linarith only [h669, h670, h693, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h695 | h695
                    · linarith only [h0, h1, h695, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h695, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h692, hc35, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h699 | h699
        · rcases m.htr 0 2 3 (by decide) (by decide) with h700 | h700
          · linarith only [h0, h1, h700, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h702 | h702
            · linarith only [h700, h702, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h704 | h704
              · linarith only [h700, h704, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h706 | h706
                · rcases m.htr 0 4 5 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h708 | h708
                    · linarith only [h0, h1, h700, h708, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h708, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h669, h707, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h706, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h713 | h713
          · linarith only [h0, h1, h713, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h715 | h715
            · linarith only [h713, h715, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h717 | h717
              · linarith only [h713, h717, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h719 | h719
                · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                    · linarith only [h0, h1, h713, h721, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h721, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h669, h720, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h719, hc35, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h726 | h726
    · rcases m.htr 0 1 4 (by decide) (by decide) with h727 | h727
      · rcases m.htr 0 1 5 (by decide) (by decide) with h728 | h728
        · rcases m.htr 0 2 3 (by decide) (by decide) with h729 | h729
          · rcases m.htr 0 2 4 (by decide) (by decide) with h730 | h730
            · rcases m.htr 0 2 5 (by decide) (by decide) with h731 | h731
              · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
                · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h738 | h738
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h742 | h742
                                    · linarith only [h0, h726, h734, h740, h742, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h0, h726, h737, h739, h742, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h726, h737, h739, h741, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h726, h737, h740, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h727, h733, h735, h739, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h726, h732, h737, h738, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                                · linarith only [h736, h737, h749, h751, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                                    · rcases h0bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h726, h736, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h727, h736, h737, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h728, h736, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h726, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h729, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h727, h736, h737, h749, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h726, h728, h736, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h727, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h730, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h726, h736, h749, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h727, h728, h736, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h728, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h731, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h732, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h733, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                    · linarith only [h736, h737, h749, h754, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                  · linarith only [h0, h727, h750, h751, h753, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h727, h733, h735, h750, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h726, h732, h734, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h726, h734, h736, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h734, h735, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h727, h730, h734, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                              · linarith only [h727, h733, h793, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h795 | h795
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h796 | h796
                                  · linarith only [h727, h733, h789, h796, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
                                    · linarith only [h727, h733, h789, h795, h798, hc23, hlam, hphi, u2ehi3]
                                    · rcases h0bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, hlam, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h733, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h726, h789, h792, h793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h733, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h726, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h729, hlam, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h727, h789, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h726, h727, h733, h789, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h727, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h730, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h733, hc03, hc45, hlam, hphi, ht34, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h733, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h728, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h731, hlam, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h732, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h727, h789, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                · linarith only [h0, h726, h791, h795, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h726, h732, h791, h792, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h828 | h828
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h829 | h829
                              · linarith only [h0, h727, h728, h733, h790, h829, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h791, h828, h829, hlam]
                            · linarith only [h0, h726, h732, h788, h828, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h726, h788, h790, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h788, h789, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h727, h730, h788, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                            · linarith only [h726, h732, h841, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                              · linarith only [h840, h841, h843, hlam]
                              · linarith only [h0, h727, h836, h838, h843, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
                            · linarith only [h726, h732, h846, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h848 | h848
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h849 | h849
                                · linarith only [h837, h840, h849, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h852 | h852
                                    · rcases h0bigk with h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h726, h732, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h727, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h729, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h730, h849, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h729, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h729, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h732, h836, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h732, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h727, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h730, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, h837, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, h732, h837, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h728, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h731, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, h837, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h836, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                    · linarith only [h0, h727, h838, h851, h852, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h727, h836, h851, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h727, h836, h838, h848, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h726, h837, h839, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h727, h731, h836, h838, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h727, h730, h837, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h888 | h888
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h889 | h889
                            · linarith only [h726, h732, h889, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h891 | h891
                              · linarith only [h727, h836, h891, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h893 | h893
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                                  · linarith only [h727, h836, h886, h894, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                                    · linarith only [h0, h727, h728, h836, h885, h886, h889, h893, h896, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h727, h886, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h732, h885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi2]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi2]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h727, h886, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h732, h885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi2]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h726, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h729, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h727, h886, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h732, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h727, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h730, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h726, h886, h888, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h836, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h728, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h731, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h728, h886, h888, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h728, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                · linarith only [h0, h726, h888, h893, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h925 | h925
                            · linarith only [h726, h732, h925, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                              · linarith only [h727, h836, h927, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h929 | h929
                                · linarith only [h729, h732, h888, h929, hc13, hc35, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                                  · linarith only [h727, h836, h886, h931, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h933 | h933
                                    · linarith only [h727, h836, h885, h888, h933, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h885, h888, h933, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h726, h885, h887, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h885, h886, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h728, h731, h885, hc23, hlam, hphi, u2ehi4]
              · linarith only [h729, h731, hc25, hlam, hphi, u2ehi2]
            · linarith only [h729, h730, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h729, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h942 | h942
          · rcases m.htr 0 2 4 (by decide) (by decide) with h943 | h943
            · rcases m.htr 0 2 5 (by decide) (by decide) with h944 | h944
              · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
                · linarith only [h726, h728, h945, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
                  · linarith only [h727, h728, h947, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h952 | h952
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h953 | h953
                            · linarith only [h726, h728, h945, h951, h953, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h726, h728, h950, h952, h953, hc35, hlam, hphi, ht23, u2ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
                            · linarith only [h726, h945, h956, hlam]
                            · linarith only [h726, h728, h949, h956, hc35, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h0, h726, h949, h951, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h949, h950, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h944, h949, hc23, hlam, hphi, u2ehi4]
              · linarith only [h942, h944, hc25, hlam, hphi, u2ehi2]
            · linarith only [h942, h943, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h942, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h965 | h965
        · rcases m.htr 0 2 3 (by decide) (by decide) with h966 | h966
          · rcases m.htr 0 2 4 (by decide) (by decide) with h967 | h967
            · rcases m.htr 0 2 5 (by decide) (by decide) with h968 | h968
              · rcases m.htr 0 3 5 (by decide) (by decide) with h969 | h969
                · rcases m.htr 0 4 5 (by decide) (by decide) with h970 | h970
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h971 | h971
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h972 | h972
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h974 | h974
                          · linarith only [h726, h727, h974, hlam]
                          · linarith only [h726, h727, h971, h974, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h726, h727, h971, h972, h973, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h967, h971, h972, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h726, h968, h969, h971, hc23, hlam, hphi, u2ehi4]
                  · linarith only [h726, h727, h969, h970, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h985 | h985
                          · linarith only [h726, h727, h985, hlam]
                          · linarith only [h726, h727, h982, h985, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h726, h727, h982, h983, h984, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h982, h983, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h967, h982, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h727, h965, h981, hlam]
              · linarith only [h967, h968, hc25, hlam, hphi, u2ehi3]
            · linarith only [h966, h967, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h966, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h995 | h995
          · rcases m.htr 0 2 4 (by decide) (by decide) with h996 | h996
            · rcases m.htr 0 2 5 (by decide) (by decide) with h997 | h997
              · rcases m.htr 0 3 5 (by decide) (by decide) with h998 | h998
                · linarith only [h726, h965, h998, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1000 | h1000
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1001 | h1001
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1003 | h1003
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1004 | h1004
                          · linarith only [h1004, h726, h727, hlam]
                          · linarith only [h1001, h1004, h726, h727, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1001, h1002, h1003, h726, h727, h997, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h1001, h1002, h726, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1001, h996, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1010 | h1010
                    · linarith only [h1000, h1010, h726, h727, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h1010, h997, hc23, hlam, hphi, u2ehi4]
              · linarith only [h995, h997, hc25, hlam, hphi, u2ehi2]
            · linarith only [h995, h996, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h995, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1016 | h1016
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1017 | h1017
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1018 | h1018
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1019 | h1019
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1020 | h1020
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1021 | h1021
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1022 | h1022
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1025 | h1025
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1027 | h1027
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1028 | h1028
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1029 | h1029
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1030 | h1030
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1031 | h1031
                                    · rcases h0bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h726, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1022, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, h1017, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, h1019, h1030, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, h1017, h1025, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1025, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1018, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1022, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1019, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, h1024, h1030, h726, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, h1017, h1025, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1020, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1021, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1022, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                    · linarith only [h1016, h1023, h1028, h1031, h726, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h1016, h1023, h1028, h1030, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h1016, h1023, h1026, h1029, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h1016, h1022, h1023, h1024, h1028, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1016, h1024, h1027, h726, hc35, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1016, h1024, h1026, h726, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h1016, h1024, h1025, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1016, h1019, h1023, h1024, h726, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1016, h1020, h1022, h1023, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1067 | h1067
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1068 | h1068
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1069 | h1069
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1070 | h1070
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1072 | h1072
                              · linarith only [h1016, h1022, h1072, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1075 | h1075
                                  · linarith only [h1016, h1022, h1068, h1075, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1077 | h1077
                                    · linarith only [h1016, h1022, h1068, h1074, h1077, hlam]
                                    · rcases h0bigk with h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h726, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, h1068, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, h1022, h1068, h726, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1022, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1017, h1068, h1072, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1018, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1018, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1018, h1022, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1019, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1022, hc03, hc45, hlam, hphi, ht34, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1022, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1017, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1020, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1021, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, h1021, h1068, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                · linarith only [h1016, h1022, h1070, h1074, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h1016, h1019, h1071, h726, hc35, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1016, h1019, h1070, h726, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1016, h1020, h1067, h1068, h1069, h726, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1017, h1020, h1067, h1068, h726, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1017, h1019, h1022, h1067, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1017, h1021, h726, hlam]
              · linarith only [h1018, h1020, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1018, h1019, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1114 | h1114
            · linarith only [h1018, h1114, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h1016, h1114, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1117 | h1117
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1118 | h1118
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1119 | h1119
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
                  · linarith only [h1016, h1017, h1121, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1125 | h1125
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1126 | h1126
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                              · linarith only [h1016, h1017, h1121, h1123, h1127, h1128, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1016, h1017, h1124, h1128, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                            · linarith only [h0, h1016, h1117, h1120, h1124, h1127, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h1016, h1124, h1126, h726, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h1016, h1119, h1120, h1124, h1125, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h1117, h1124, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1016, h1118, h1123, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h1016, h1120, h1136, h726, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1139 | h1139
                      · linarith only [h1016, h1120, h1139, h726, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h1117, h1139, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1117, h1138, hlam]
              · linarith only [h1117, h1119, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1117, h1118, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1145 | h1145
            · linarith only [h1117, h1145, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h1016, h1145, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1148 | h1148
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1149 | h1149
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1150 | h1150
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1151 | h1151
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1152 | h1152
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1153 | h1153
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1155 | h1155
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1156 | h1156
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1157 | h1157
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1158 | h1158
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1159 | h1159
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1160 | h1160
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1161 | h1161
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1162 | h1162
                                    · rcases h0bigk with h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h726, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1016, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1016, h1154, h1157, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1016, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1149, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1016, h1148, h1156, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1149, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1150, hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, h726, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1150, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1151, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1152, hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1153, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                    · rcases h0bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h726, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1156, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, h1149, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi2]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, h1016, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1156, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1149, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1156, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1150, hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1151, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1152, hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1153, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                  · linarith only [h1016, h1148, h1154, h1157, h1159, h1161, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                                    · rcases h0bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h726, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1154, h1157, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, h1148, h726, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, h1016, h1148, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, h1151, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, h1151, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1149, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, h1156, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1150, hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1151, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1152, hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1153, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                    · linarith only [h1160, h1216, h1217, hc24, hlam, hphi, u2ehi2]
                                  · linarith only [h0, h1148, h1159, h1216, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h1016, h1148, h1153, h1159, hlam]
                            · linarith only [h1016, h1148, h1156, h1157, h1158, hc35, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h1148, h1156, h1157, h726, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h0, h1149, h1156, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h1148, h1151, h1154, h1155, h726, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1148, h1149, h1151, h1154, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h1016, h1148, h1153, hlam]
                · linarith only [h1148, h1152, h726, hlam]
              · linarith only [h1149, h1151, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1149, h1150, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1256 | h1256
            · linarith only [h1149, h1256, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1258 | h1258
              · linarith only [h1149, h1258, hc23, hlam, hphi, u2ehi4]
              · linarith only [h0, h1148, h1258, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1261 | h1261
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1262 | h1262
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1263 | h1263
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1264 | h1264
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1265 | h1265
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1266 | h1266
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1268 | h1268
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1270 | h1270
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1271 | h1271
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1273 | h1273
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                                    · rcases h0bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h726, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1148, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1148, h1264, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1148, h1265, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h726, hc01, hc13, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1261, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1261, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi3]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1261, h1263, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi4]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1262, hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, h1263, h1266, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi4]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1148, hc01, hc15, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1263, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1264, hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1265, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                    · rcases h0bigk with h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h726, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1148, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, h1261, h1272, h1273, h1274, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1266, h726, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1261, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1262, h1266, h1273, h1274, h726, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1263, h1266, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1301_1, u2ehi4]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, h1266, h1269, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1262, hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, h1263, h1266, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1301_1, u2ehi4]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1148, h1266, h1269, h1271, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1263, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1264, hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1265, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1327 | h1327
                                    · linarith only [h1273, h1327, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h726, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1148, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, h1265, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1266, h726, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1261, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1265, h1266, h1273, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1265, h1266, h1273, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, h1266, h1269, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1262, hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, h1265, h1266, h1269, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1148, h1266, h1269, h1271, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1263, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1264, hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1265, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1355 | h1355
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1356 | h1356
                                    · rcases h0bigk with h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h726, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1148, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1266, h726, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1261, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1262, h1266, h1355, h726, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1263, h1266, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1357_1, u2ehi4]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, h1266, h1269, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1262, hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, h1263, h1266, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1357_1, u2ehi4]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1148, h1266, h1269, h1271, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1263, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1264, hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1265, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                    · linarith only [h1272, h1356, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1384 | h1384
                                    · linarith only [h1266, h1269, h1272, h1355, h1384, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h1272, h1384, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1016, h1265, h1271, hlam]
                            · linarith only [h1264, h1270, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1389 | h1389
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1390 | h1390
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1391 | h1391
                                · linarith only [h1261, h1264, h1269, h1391, h726, hc02, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1393 | h1393
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1394 | h1394
                                    · rcases h0bigk with h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h726, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1148, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, h1264, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, h1263, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1395_1, u2ehi4]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1269, h726, hc01, hc34, hlam, hphi, ht12, ht23, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1261, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1269, h726, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1263, h1269, h726, hc34, hlam, hphi, ht23, p1395_1, u2ehi4]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, h1269, hc01, hc34, hlam, hphi, ht12, ht23, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1262, hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, h1269, hc03, hc34, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, h1263, h1269, hc34, hlam, hphi, ht23, p1395_1, u2ehi4]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1148, hc01, hc15, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1263, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1264, hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1265, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                    · linarith only [h1269, h1394, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h1264, h1265, h1269, h1391, h1393, h726, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h1016, h1264, h1265, h1269, h1390, h726, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1264, h1389, h726, hlam]
                        · linarith only [h0, h1261, h1268, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h1263, h1267, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1266, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1430 | h1430
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1432 | h1432
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1434 | h1434
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1435 | h1435
                                  · linarith only [h1262, h1265, h1435, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1437 | h1437
                                    · linarith only [h1262, h1265, h1434, h1437, hlam]
                                    · rcases h0bigk with h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h726, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1016, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1148, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, h1261, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi2]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, h1262, h1265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1428, h726, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1261, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1262, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1262, h1265, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1016, h1428, h1431, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1262, hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, h1428, h1431, h1433, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, h1428, h1431, h1433, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1263, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1264, hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, h1428, h1431, h1433, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1465 | h1465
                                  · linarith only [h0, h1016, h1262, h1265, h1465, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1467 | h1467
                                    · linarith only [h1262, h1265, h1434, h1467, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1434, h1467, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1471 | h1471
                                  · linarith only [h1016, h1433, h1470, h1471, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1473 | h1473
                                    · linarith only [h1016, h1262, h1433, h1470, h1473, hc23, hlam, hphi, u2ehi3]
                                    · rcases h0bigk with h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h726, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1148, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, h1262, h1265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1428, h726, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1261, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1262, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1262, h1265, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1262, hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, h1433, hc03, hc45, hlam, hphi, ht34, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1265, hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1148, h1433, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1263, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1264, hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, h1264, h1428, h726, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                · linarith only [h1431, h1433, h1470, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h1264, h1432, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1503 | h1503
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
                              · linarith only [h1262, h1265, h1431, h1504, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h1431, h1503, h1504, hlam]
                            · linarith only [h1264, h1503, h726, hlam]
                        · linarith only [h0, h1263, h1430, hlam]
                      · linarith only [h0, h1263, h1429, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1428, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1511 | h1511
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1512 | h1512
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1513 | h1513
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1514 | h1514
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1515 | h1515
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1516 | h1516
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1517 | h1517
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1518 | h1518
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1520 | h1520
                                    · linarith only [h1261, h1264, h1512, h1516, h1518, h1520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h1261, h1264, h1512, h1516, h1518, h1519, h1520, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1523 | h1523
                                    · linarith only [h1519, h1523, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h1264, h1511, h1523, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1526 | h1526
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1527 | h1527
                                    · rcases h0bigk with h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h726, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1148, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, h1261, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1512, h726, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1261, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1264, h1511, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1264, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1262, hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, h1261, h1512, h1515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, h1261, h1264, h1512, h1515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1148, hc01, hc15, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1263, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1261, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1511, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                    · linarith only [h1518, h1527, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1555 | h1555
                                    · linarith only [h1512, h1515, h1526, h1555, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · linarith only [h1518, h1555, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1016, h1511, h1517, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1559 | h1559
                              · linarith only [h1515, h1516, h1559, hlam]
                              · linarith only [h1016, h1511, h1559, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1562 | h1562
                            · linarith only [h1261, h1264, h1515, h1562, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1564 | h1564
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1565 | h1565
                                · linarith only [h1261, h1515, h1565, h726, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1567 | h1567
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1568 | h1568
                                    · rcases h0bigk with h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h726, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1148, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, h1261, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h726, hc01, hc13, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1261, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1262, h1567, hc03, hc45, hlam, hphi, ht0b, ht5b, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1264, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, h1515, hc01, hc34, hlam, hphi, ht12, ht23, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1262, hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, h1261, h1515, hc34, hlam, hphi, ht23, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, h1261, h1264, h1515, hc34, hlam, hphi, ht23, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1148, h1515, h1564, hc01, hc34, hlam, hphi, ht12, ht23, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1263, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1148, h1261, h1515, h1564, hc34, hlam, hphi, ht23, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1511, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                    · linarith only [h1016, h1511, h1515, h1568, hlam]
                                  · linarith only [h1016, h1511, h1515, h1565, h1567, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h1016, h1511, h1564, hlam]
                        · linarith only [h0, h1261, h1514, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h1263, h1513, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1512, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1601 | h1601
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1602 | h1602
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1603 | h1603
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1604 | h1604
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1605 | h1605
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1606 | h1606
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1607 | h1607
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1608 | h1608
                                  · linarith only [h1262, h1511, h1608, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1610 | h1610
                                    · linarith only [h1261, h1264, h1511, h1601, h1605, h1607, h1610, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h726, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1016, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1148, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, h1261, h1607, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1612_1, u2ehi3]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1601, h726, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1261, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1262, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1612_1, u2ehi3]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1264, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1016, h1601, h1604, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1262, hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1511, h1601, h1604, h1606, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1511, hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1264, h1601, h1604, h1606, h1610, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1263, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1261, h1264, h1601, h1604, h1606, h1607, h1610, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1612_1, u2ehi3]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1264, h1601, h1604, h1606, h1610, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1638 | h1638
                                  · linarith only [h0, h1016, h1262, h1511, h1638, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1640 | h1640
                                    · linarith only [h1262, h1511, h1607, h1640, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1607, h1640, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1643 | h1643
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1644 | h1644
                                  · linarith only [h1016, h1606, h1643, h1644, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1646 | h1646
                                    · linarith only [h1016, h1261, h1264, h1601, h1605, h1606, h1643, h1646, hc01, hc12, hlam, hphi]
                                    · rcases h0bigk with h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h726, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1016, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1148, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, h1261, h1643, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, h1605, hc01, hc13, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1261, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1262, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1262, hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1016, h1606, hc03, hc45, hlam, hphi, ht34, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1511, hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, h1601, h1605, hc01, hc12, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1263, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1261, h1264, h1601, h1605, h1643, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, h1601, h1605, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                · linarith only [h1604, h1606, h1643, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1675 | h1675
                              · linarith only [h1262, h1511, h1604, h1605, h1675, hc35, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1677 | h1677
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1678 | h1678
                                  · linarith only [h1016, h1675, h1677, h1678, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1680 | h1680
                                    · linarith only [h1016, h1261, h1262, h1605, h1675, h1677, h1680, h726, hc35, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h726, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1016, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, h1261, h1677, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1682_1, u2ehi3]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1605, h1680, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1261, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1262, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1682_1, u2ehi3]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1264, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1262, hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1016, h1604, h1605, h1680, hc03, hc45, hlam, hphi, ht34, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1511, hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, h1605, h1680, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1263, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, h1261, h1605, h1677, h1680, hc45, hlam, hphi, ht23, ht34, p1682_1, u2ehi3]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, h1605, h1680, hc04, hc45, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                · linarith only [h1604, h1605, h1677, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1709 | h1709
                            · linarith only [h1261, h1264, h1604, h1709, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1711 | h1711
                              · linarith only [h1262, h1511, h1604, h1711, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1713 | h1713
                                · linarith only [h1261, h1604, h1713, h726, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1715 | h1715
                                  · linarith only [h1604, h1711, h1715, h726, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1717 | h1717
                                    · linarith only [h1016, h1262, h1711, h1717, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h1604, h1717, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h1263, h1603, hlam]
                      · linarith only [h0, h1263, h1602, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1601, hc23, hlam, hphi, u2ehi4]
              · linarith only [h1261, h1263, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1261, h1262, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1725 | h1725
            · linarith only [h1261, h1725, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1727 | h1727
              · linarith only [h1261, h1727, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1729 | h1729
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1730 | h1730
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1732 | h1732
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1733 | h1733
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1734 | h1734
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1735 | h1735
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1736 | h1736
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1737 | h1737
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1738 | h1738
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1739 | h1739
                                    · rcases h0bigk with h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h0, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h726, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1016, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1148, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1727, h1731, h1737, h1738, hc01, hc12, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1727, hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1731, hc01, hc12, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1727, h1730, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1727, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1016, h1734, hc01, hc13, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, h1731, h1737, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, h1727, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1729, h1731, h726, hc01, hc12, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1727, h1731, h1737, h1738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1729, hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1730, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                    · rcases h0bigk with h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h0, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h726, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1016, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1148, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1727, hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1016, h1731, h1734, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, h1731, h1737, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, h1727, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1729, h1731, h726, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1727, h1731, h1737, h1738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1729, hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1730, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                  · linarith only [h1725, h1738, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1737, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1725, h1730, h1732, h1736, hc01, hc12, hlam, hphi]
                            · linarith only [h1729, h1735, h726, hlam]
                          · linarith only [h1261, h1731, h1734, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1732, h1733, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1261, h1731, h1732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1799 | h1799
                      · linarith only [h1731, h1799, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1801 | h1801
                        · linarith only [h1731, h1801, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1803 | h1803
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1804 | h1804
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1805 | h1805
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1806 | h1806
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1807 | h1807
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1808 | h1808
                                    · rcases h0bigk with h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h0, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h726, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1148, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h0, h1801, h1806, h1807, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1261, hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1725, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1727, hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1731, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1731, h726, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1727, h1731, h726, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h1803, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h1803, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h1803, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1727, h1731, h1803, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1729, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1148, h1731, h1803, h1805, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1729, hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1730, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                    · rcases h0bigk with h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h0, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h726, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1148, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h0, h1801, h1806, h1807, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1261, hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1725, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1727, hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1731, h726, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1148, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h1803, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h1803, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h1803, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1727, h1731, h1803, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1729, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1148, h1731, h1803, h1805, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1729, hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1730, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                  · linarith only [h1725, h1807, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h0, h1731, h1806, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1016, h1730, h1805, hlam]
                            · linarith only [h1729, h1804, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1865 | h1865
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1866 | h1866
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1867 | h1867
                                · linarith only [h1803, h1867, h726, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1261, h1867, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1730, h1866, hlam]
                            · linarith only [h1729, h1865, h726, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1872 | h1872
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1873 | h1873
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1874 | h1874
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1875 | h1875
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1876 | h1876
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1877 | h1877
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1878 | h1878
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1879 | h1879
                                  · linarith only [h1725, h1730, h1872, h1878, h1879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1725, h1879, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1878, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1725, h1873, h1877, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1729, h1876, h726, hlam]
                          · linarith only [h1261, h1872, h1875, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1261, h1872, h1874, hc25, hlam, hphi, u2ehi0]
                      · linarith only [h1261, h1872, h1873, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1888 | h1888
                      · linarith only [h1872, h1888, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1890 | h1890
                        · linarith only [h1872, h1890, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1892 | h1892
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1893 | h1893
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1894 | h1894
                              · linarith only [h1725, h1730, h1888, h1894, hc24, hlam, hphi, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1896 | h1896
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1897 | h1897
                                  · linarith only [h1888, h1894, h1896, h1897, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h1725, h1897, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1896, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1729, h1893, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1902 | h1902
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1903 | h1903
                              · linarith only [h1725, h1730, h1888, h1903, hc24, hlam, hphi, u2ehi0]
                              · linarith only [h1892, h1902, h1903, hlam]
                            · linarith only [h1729, h1902, h726, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1907 | h1907
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1908 | h1908
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1909 | h1909
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1910 | h1910
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1911 | h1911
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1912 | h1912
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1913 | h1913
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1915 | h1915
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1916 | h1916
                                    · linarith only [h1729, h1908, h1914, h1916, h726, hc01, hc12, hlam, hphi]
                                    · linarith only [h1261, h1725, h1729, h1907, h1908, h1914, h1916, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1725, h1915, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1914, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1725, h1907, h1909, h1913, hc01, hc12, hlam, hphi]
                            · linarith only [h1261, h1908, h1912, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1261, h1908, h1911, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1909, h1910, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1261, h1908, h1909, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1926 | h1926
                      · linarith only [h1908, h1926, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1928 | h1928
                        · linarith only [h1908, h1928, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1930 | h1930
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1931 | h1931
                            · linarith only [h1261, h1729, h1908, h1931, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1933 | h1933
                              · linarith only [h1930, h1931, h1933, hlam]
                              · linarith only [h1016, h1907, h1933, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1936 | h1936
                            · linarith only [h1261, h1729, h1908, h1936, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1938 | h1938
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1939 | h1939
                                · linarith only [h1930, h1939, h726, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1261, h1939, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1907, h1938, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1943 | h1943
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1944 | h1944
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1945 | h1945
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1946 | h1946
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1947 | h1947
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1948 | h1948
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1949 | h1949
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1950 | h1950
                                  · linarith only [h1725, h1907, h1943, h1949, h1950, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1725, h1946, h1948, h1950, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · linarith only [h1261, h1949, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1725, h1944, h1948, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1261, h1943, h1947, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1261, h1943, h1946, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1261, h1943, h1945, hc25, hlam, hphi, u2ehi0]
                      · linarith only [h1261, h1943, h1944, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1959 | h1959
                      · linarith only [h1943, h1959, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1961 | h1961
                        · linarith only [h1943, h1961, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1963 | h1963
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1964 | h1964
                            · linarith only [h1261, h1729, h1943, h1964, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1966 | h1966
                              · linarith only [h1725, h1907, h1963, h1964, h1966, hc35, hlam, hphi, ht23, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1968 | h1968
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1969 | h1969
                                  · linarith only [h1959, h1966, h1969, hc24, hlam, hphi, u2ehi1]
                                  · linarith only [h1725, h1969, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1963, h1964, h1968, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1973 | h1973
                            · linarith only [h1261, h1729, h1963, h1973, hc34, hlam, hphi, ht23, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1975 | h1975
                              · linarith only [h1725, h1907, h1963, h1975, hc34, hlam, hphi, ht23, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1977 | h1977
                                · linarith only [h1963, h1977, h726, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1261, h1977, hc34, hlam, hphi, ht23, u2ehi0]

theorem n7l_sAA2_H_I_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases h2bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h13 | h13
                · rcases p11_3 (m.d 1 2) (by simp) with h14 | h14
                  · linarith only [h14, hlam, p11_0]
                  · rcases p11_3 (m.d 2 3) (by simp) with h16 | h16
                    · linarith only [h16, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
                    · rcases p11_3 (m.d 2 4) (by simp) with h18 | h18
                      · linarith only [h18, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
                      · rcases p11_3 (m.d 2 5) (by simp) with h20 | h20
                        · linarith only [h20, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
                        · rcases h2emax with h22 | h22 | h22 | h22 | h22
                          · linarith only [h22, hlam, ht12, p11_1, u1ehi1]
                          · linarith only [h22, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h29 | h29
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                                                      · linarith only [h25, h32, h38, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h25, h32, h35, h38, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                                                      · linarith only [h25, h32, h41, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h25, h32, h35, h41, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                                                    · linarith only [h35, h36, h44, hlam]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                                                      · linarith only [h25, h32, h46, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h25, h34, h35, h36, h46, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                                      · linarith only [h35, h49, h51, hc23, hlam, hphi, ht12, u1ehi4]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                                                        · linarith only [h25, h33, h51, h53, hc01, hc35, hlam, hphi, ht0b, ht5b, p11_1]
                                                        · linarith only [h35, h49, h53, hc23, hc34, hlam, hphi]
                                                    · linarith only [h35, h49, h50, hlam]
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                                                      · linarith only [h35, h58, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                                        · linarith only [h25, h33, h49, h58, h60, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                                          · linarith only [h25, h33, h62, hc01, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                                                          · linarith only [h25, h33, h57, h58, h62, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                                                      · linarith only [h35, h65, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                                                        · linarith only [h25, h33, h49, h65, h67, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                                                          · linarith only [h25, h33, h57, h69, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                                                            · linarith only [h35, h57, h71, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h35, h71, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                              · linarith only [h34, h9, hlam]
                                            · linarith only [h33, h7, hlam]
                                          · linarith only [h32, h5, hlam]
                                        · linarith only [h31, hc12, hc25, hlam, hphi, p11_1]
                                      · linarith only [h30, hc12, hc24, hlam, hphi, p11_1]
                                    · linarith only [h29, hc12, hc23, hlam, hphi, p11_1]
                                  · linarith only [h25, h28, hc15, hlam, hphi, p11_1, u1ehi1]
                                · linarith only [h25, h27, h7, hlam, p11_1]
                              · linarith only [h25, h26, hc13, hlam, hphi, p11_1, u1ehi1]
                            · linarith only [h25, hlam, p0_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h84 | h84
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h85 | h85
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h86 | h86
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h87 | h87
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h88 | h88
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h89 | h89
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h90 | h90
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                                                      · linarith only [h91, h97, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h84, h91, h94, h97, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                                                      · linarith only [h100, h84, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h100, h84, h91, h94, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                                                    · linarith only [h103, h94, h95, hlam]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                                                      · linarith only [h105, h84, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h105, h84, h93, h94, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                                                      · linarith only [h108, h110, h94, hc23, hlam, hphi, ht12, u1ehi4]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                                                        · linarith only [h110, h112, h84, h92, hc01, hc35, hlam, hphi, ht0b, ht5b, p11_1]
                                                        · linarith only [h108, h112, h94, hc23, hc34, hlam, hphi]
                                                    · linarith only [h108, h109, h94, hlam]
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                                                      · linarith only [h117, h94, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                                                        · linarith only [h108, h117, h119, h84, h92, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                                                          · linarith only [h121, h84, h92, hc01, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                                                          · linarith only [h116, h117, h121, h84, h92, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                                                      · linarith only [h124, h94, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                                                        · linarith only [h108, h126, hc23, hlam, hphi, ht12, u1ehi2]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                                                          · linarith only [h116, h128, h84, h92, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                                                            · linarith only [h116, h130, h94, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h130, h94, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                              · linarith only [h9, h93, hlam]
                                            · linarith only [h7, h92, hlam]
                                          · linarith only [h5, h91, hlam]
                                        · linarith only [h90, hc12, hc25, hlam, hphi, p11_1]
                                      · linarith only [h89, hc12, hc24, hlam, hphi, p11_1]
                                    · linarith only [h88, hc12, hc23, hlam, hphi, p11_1]
                                  · linarith only [h84, h87, hc15, hlam, hphi, p11_1, u1ehi1]
                                · linarith only [h84, h86, hc14, hlam, hphi, p11_1, u1ehi1]
                              · linarith only [h84, h85, hc13, hlam, hphi, p11_1, u1ehi1]
                            · linarith only [h84, hlam, p0_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h143 | h143
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h144 | h144
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h146 | h146
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h147 | h147
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h148 | h148
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h149 | h149
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                                              · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                                                      · linarith only [h150, h156, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h143, h150, h153, h156, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                                                      · linarith only [h143, h150, h159, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h143, h150, h153, h159, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                                                    · linarith only [h153, h154, h162, hlam]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                                                      · linarith only [h143, h150, h164, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                      · linarith only [h143, h152, h153, h154, h164, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                                                      · linarith only [h153, h167, h169, hc23, hlam, hphi, ht12, u1ehi4]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                                                        · linarith only [h143, h151, h169, h171, hc01, hc35, hlam, hphi, ht0b, ht5b, p11_1]
                                                        · linarith only [h153, h167, h171, hc23, hc34, hlam, hphi]
                                                    · linarith only [h153, h167, h168, hlam]
                                                  · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                                                      · linarith only [h153, h176, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                                        · linarith only [h143, h151, h167, h176, h178, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                                                          · linarith only [h143, h151, h180, hc01, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                                                          · linarith only [h143, h151, h175, h176, h180, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1]
                                                    · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                                                      · linarith only [h153, h183, hc23, hlam, hphi, ht12, u1ehi2]
                                                      · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                                                        · linarith only [h143, h151, h167, h183, h185, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi2]
                                                        · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                                                          · linarith only [h143, h151, h175, h187, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                                                            · linarith only [h153, h175, h189, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                                            · linarith only [h153, h189, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                              · linarith only [h152, h9, hlam]
                                            · linarith only [h151, h7, hlam]
                                          · linarith only [h150, h5, hlam]
                                        · linarith only [h149, hc12, hc25, hlam, hphi, p11_1]
                                      · linarith only [h148, hc12, hc24, hlam, hphi, p11_1]
                                    · linarith only [h147, hc12, hc23, hlam, hphi, p11_1]
                                  · linarith only [h143, h146, hc15, hlam, hphi, p11_1, u1ehi1]
                                · linarith only [h143, h145, h7, hlam, p11_1]
                              · linarith only [h143, h144, hc13, hlam, hphi, p11_1, u1ehi1]
                            · linarith only [h143, hlam, p0_0]
                · linarith only [h13, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h203 | h203
                · rcases p11_3 (m.d 1 2) (by simp) with h204 | h204
                  · linarith only [h204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h206 | h206
                    · linarith only [h206, hlam, p11_0]
                    · rcases p11_3 (m.d 2 4) (by simp) with h208 | h208
                      · linarith only [h204, h208, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
                      · rcases p11_3 (m.d 2 5) (by simp) with h210 | h210
                        · linarith only [h204, h210, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
                        · rcases h2emax with h212 | h212 | h212 | h212 | h212
                          · linarith only [h204, h212, hlam, ht12, p11_1, u1ehi1]
                          · linarith only [h212, hlam, ht12, u1ehi1]
                          · linarith only [h204, h212, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h216 | h216
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h217 | h217
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h218 | h218
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h219 | h219
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h220 | h220
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h221 | h221
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h222 | h222
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                                          · linarith only [h204, h223, hlam]
                                          · linarith only [h223, h5, hlam]
                                        · linarith only [h210, h222, hlam, p11_1]
                                      · linarith only [h204, h212, h221, hlam, ht12, p11_1, u1ehi1]
                                    · linarith only [h220, hlam, p11_0]
                                  · linarith only [h204, h219, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                                · linarith only [h204, h216, h218, h7, hlam, p11_1]
                              · linarith only [h204, h216, h217, h5, hlam, p11_1]
                            · linarith only [h216, hlam, p0_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h233 | h233
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h234 | h234
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h235 | h235
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h236 | h236
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h237 | h237
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h238 | h238
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h239 | h239
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                                          · linarith only [h204, h240, hlam]
                                          · linarith only [h240, h5, hlam]
                                        · linarith only [h204, h212, h239, hlam, ht12, p11_1, u1ehi1]
                                      · linarith only [h204, h238, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
                                    · linarith only [h237, hlam, p11_0]
                                  · linarith only [h204, h236, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi0]
                                · linarith only [h204, h233, h235, h7, hlam, p11_1]
                              · linarith only [h204, h233, h234, h5, hlam, p11_1]
                            · linarith only [h233, hlam, p0_0]
                · linarith only [h203, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h251 | h251
                · rcases p11_3 (m.d 1 2) (by simp) with h252 | h252
                  · linarith only [h252, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h254 | h254
                    · linarith only [h252, h254, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
                    · rcases p11_3 (m.d 2 4) (by simp) with h256 | h256
                      · linarith only [h256, hlam, p11_0]
                      · rcases p11_3 (m.d 2 5) (by simp) with h258 | h258
                        · linarith only [h252, h258, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
                        · rcases h2emax with h260 | h260 | h260 | h260 | h260
                          · linarith only [h252, h260, hlam, ht12, p11_1, u1ehi1]
                          · linarith only [h260, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h263 | h263
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h264 | h264
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h265 | h265
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h266 | h266
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h267 | h267
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h268 | h268
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h269 | h269
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                                            · linarith only [h252, h271, hlam]
                                            · linarith only [h271, h7, hlam]
                                          · linarith only [h270, h5, hlam]
                                        · linarith only [h258, h269, hlam, p11_1]
                                      · linarith only [h268, hlam, p11_0]
                                    · linarith only [h252, h267, hc12, hc23, hlam, hphi, p11_1]
                                  · linarith only [h252, h263, h266, h9, hlam, p11_1]
                                · linarith only [h252, h263, h265, h7, hlam, p11_1]
                              · linarith only [h252, h263, h264, hc13, hlam, hphi, p11_1, u1ehi1]
                            · linarith only [h263, hlam, p0_0]
                          · linarith only [h252, h260, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h283 | h283
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h284 | h284
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h285 | h285
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h286 | h286
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h287 | h287
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h288 | h288
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h289 | h289
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
                                            · linarith only [h252, h291, hlam]
                                            · linarith only [h291, h7, hlam]
                                          · linarith only [h290, h5, hlam]
                                        · linarith only [h260, h289, hc02, hlam]
                                      · linarith only [h288, hlam, p11_0]
                                    · linarith only [h252, h287, h5, hc23, hlam, hphi, ht12, p11_1, u1ehi2]
                                  · linarith only [h252, h283, h286, h9, hlam, p11_1]
                                · linarith only [h252, h283, h285, h7, hlam, p11_1]
                              · linarith only [h252, h283, h284, h5, hlam, p11_1]
                            · linarith only [h283, hlam, p0_0]
                · linarith only [h251, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h303 | h303
                · rcases p11_3 (m.d 1 2) (by simp) with h304 | h304
                  · linarith only [h304, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · rcases p11_3 (m.d 2 3) (by simp) with h306 | h306
                    · linarith only [h304, h306, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
                    · rcases p11_3 (m.d 2 4) (by simp) with h308 | h308
                      · linarith only [h304, h308, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
                      · rcases p11_3 (m.d 2 5) (by simp) with h310 | h310
                        · linarith only [h310, hlam, p11_0]
                        · rcases h2emax with h312 | h312 | h312 | h312 | h312
                          · linarith only [h304, h312, hlam, ht12, p11_1, u1ehi1]
                          · linarith only [h312, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h315 | h315
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h316 | h316
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h317 | h317
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h318 | h318
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h319 | h319
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h320 | h320
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h321 | h321
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                                              · linarith only [h304, h324, hlam]
                                              · linarith only [h324, h9, hlam]
                                            · linarith only [h323, h7, hlam]
                                          · linarith only [h322, h5, hlam]
                                        · linarith only [h321, hlam, p11_0]
                                      · linarith only [h304, h320, hc12, hc24, hlam, hphi, p11_1]
                                    · linarith only [h304, h319, hc12, hc23, hlam, hphi, p11_1]
                                  · linarith only [h304, h315, h318, h9, hlam, p11_1]
                                · linarith only [h304, h315, h317, hc14, hlam, hphi, p11_1, u1ehi1]
                              · linarith only [h304, h315, h316, hc13, hlam, hphi, p11_1, u1ehi1]
                            · linarith only [h315, hlam, p0_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h336 | h336
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h337 | h337
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h338 | h338
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h339 | h339
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h340 | h340
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h341 | h341
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h342 | h342
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
                                              · linarith only [h304, h345, hlam]
                                              · linarith only [h345, h9, hlam]
                                            · linarith only [h344, h7, hlam]
                                          · linarith only [h343, h5, hlam]
                                        · linarith only [h342, hlam, p11_0]
                                      · linarith only [h304, h341, hc12, hc24, hlam, hphi, p11_1]
                                    · linarith only [h304, h340, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
                                  · linarith only [h304, h336, h339, h9, hlam, p11_1]
                                · linarith only [h304, h336, h338, hc14, hlam, hphi, p11_1, u1ehi1]
                              · linarith only [h304, h336, h337, hc13, hlam, hphi, p11_1, u1ehi1]
                            · linarith only [h336, hlam, p0_0]
                          · linarith only [h304, h312, hlam, ht12, u1ehi1]
                · linarith only [h303, hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h364 | h364
                · linarith only [h364, hlam, p11_0]
                · rcases p11_3 (m.d 1 2) (by simp) with h366 | h366
                  · linarith only [h366, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h366, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc23, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h371 | h371
                · rcases p11_3 (m.d 1 2) (by simp) with h372 | h372
                  · linarith only [h372, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h372, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
                · rcases p11_3 (m.d 1 2) (by simp) with h375 | h375
                  · linarith only [h371, h375, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h375, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h378 | h378
                · rcases p11_3 (m.d 1 2) (by simp) with h379 | h379
                  · linarith only [h379, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h379, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
                · rcases p11_3 (m.d 1 2) (by simp) with h382 | h382
                  · linarith only [h378, h382, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h382, hc23, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h385 | h385
                · linarith only [h385, hlam, p11_0]
                · rcases p11_3 (m.d 1 2) (by simp) with h387 | h387
                  · linarith only [h387, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h387, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc24, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h391 | h391
                · rcases p11_3 (m.d 1 2) (by simp) with h392 | h392
                  · linarith only [h392, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h392, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
                · rcases p11_3 (m.d 1 2) (by simp) with h395 | h395
                  · linarith only [h391, h395, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h395, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h399 | h399
                · rcases p11_3 (m.d 1 2) (by simp) with h400 | h400
                  · linarith only [h400, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p11_1]
                  · linarith only [h400, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
                · rcases p11_3 (m.d 1 2) (by simp) with h403 | h403
                  · linarith only [h399, h403, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h403, hc24, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h406 | h406
                · linarith only [h406, hlam, p11_0]
                · rcases p11_3 (m.d 1 2) (by simp) with h408 | h408
                  · linarith only [h408, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h408, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hc25, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h412 | h412
                · rcases p11_3 (m.d 1 2) (by simp) with h413 | h413
                  · linarith only [h413, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h413, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
                · rcases p11_3 (m.d 1 2) (by simp) with h416 | h416
                  · linarith only [h412, h416, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h416, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                rcases p11_3 (m.d 0 2) (by simp) with h419 | h419
                · rcases p11_3 (m.d 1 2) (by simp) with h420 | h420
                  · linarith only [h420, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h420, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
                · rcases p11_3 (m.d 1 2) (by simp) with h423 | h423
                  · linarith only [h419, h423, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p11_1]
                  · linarith only [h423, hc25, hlam, hphi, ht12, p11_1, u1ehi1]
              · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                linarith only [hlam, p11_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h428 | h428
    · rcases p0_3 (m.d 1 2) (by simp) with h429 | h429
      · linarith only [h429, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h431 | h431
        · linarith only [h431, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h433 | h433
          · linarith only [h433, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h435 | h435
            · linarith only [h435, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases h2bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h439 | h439
                · rcases p437_3 (m.d 1 2) (by simp) with h440 | h440
                  · linarith only [h440, hlam, p437_0]
                  · rcases p437_3 (m.d 2 3) (by simp) with h442 | h442
                    · linarith only [h442, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                    · rcases p437_3 (m.d 2 4) (by simp) with h444 | h444
                      · linarith only [h444, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                      · rcases p437_3 (m.d 2 5) (by simp) with h446 | h446
                        · linarith only [h446, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
                        · rcases h2emax with h448 | h448 | h448 | h448 | h448
                          · linarith only [h448, hlam, ht12, p437_1, u1ehi1]
                          · linarith only [h448, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h451 | h451
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h452 | h452
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h453 | h453
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h454 | h454
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h455 | h455
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h456 | h456
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h457 | h457
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                                          · linarith only [h429, h458, hlam]
                                          · linarith only [h442, h458, hlam]
                                        · linarith only [h446, h457, hlam, p437_1]
                                      · linarith only [h444, h456, hlam, p437_1]
                                    · linarith only [h448, h455, hlam, ht12, p437_1, u1ehi1]
                                  · linarith only [h435, h451, h454, hc13, hlam, hphi, p437_1, u1ehi1]
                                · linarith only [h433, h453, hlam, p0_1]
                              · linarith only [h452, hlam, p0_0]
                            · linarith only [h451, hlam, p437_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h468 | h468
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h469 | h469
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h470 | h470
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h471 | h471
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h472 | h472
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h473 | h473
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h474 | h474
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                                          · linarith only [h429, h475, hlam]
                                          · linarith only [h442, h475, hlam]
                                        · linarith only [h446, h474, hlam, p437_1]
                                      · linarith only [h448, h473, hlam, ht12, p437_1, u1ehi1]
                                    · linarith only [h472, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                                  · linarith only [h435, h471, hlam, p0_1]
                                · linarith only [h433, h470, hlam, p0_1]
                              · linarith only [h469, hlam, p0_0]
                            · linarith only [h468, hlam, p437_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h485 | h485
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h486 | h486
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h487 | h487
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h488 | h488
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h489 | h489
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h490 | h490
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h491 | h491
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                                          · linarith only [h429, h492, hlam]
                                          · linarith only [h442, h492, hlam]
                                        · linarith only [h448, h491, hlam, ht12, p437_1, u1ehi1]
                                      · linarith only [h490, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                                    · linarith only [h442, h489, hlam, p437_1]
                                  · linarith only [h435, h488, hlam, p0_1]
                                · linarith only [h433, h487, hlam, p0_1]
                              · linarith only [h486, hlam, p0_0]
                            · linarith only [h485, hlam, p437_0]
                · linarith only [h439, hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h503 | h503
                · rcases p437_3 (m.d 1 2) (by simp) with h504 | h504
                  · linarith only [h429, h504, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p437_1]
                  · rcases p437_3 (m.d 2 3) (by simp) with h506 | h506
                    · linarith only [h506, hlam, p437_0]
                    · rcases p437_3 (m.d 2 4) (by simp) with h508 | h508
                      · linarith only [h504, h508, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                      · rcases p437_3 (m.d 2 5) (by simp) with h510 | h510
                        · linarith only [h504, h510, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
                        · rcases h2emax with h512 | h512 | h512 | h512 | h512
                          · linarith only [h504, h512, hlam, ht12, p437_1, u1ehi1]
                          · linarith only [h512, hlam, ht12, u1ehi1]
                          · linarith only [h504, h512, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h516 | h516
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h517 | h517
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h518 | h518
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h519 | h519
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h520 | h520
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h521 | h521
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h522 | h522
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                                          · linarith only [h429, h523, hlam]
                                          · linarith only [h523, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi1]
                                        · linarith only [h510, h522, hlam, p437_1]
                                      · linarith only [h512, h521, hc02, hlam]
                                    · linarith only [h520, hlam, p437_0]
                                  · linarith only [h435, h519, hlam, p0_1]
                                · linarith only [h433, h518, hlam, p0_1]
                              · linarith only [h517, hlam, p0_0]
                            · linarith only [h504, h516, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h533 | h533
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h534 | h534
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h535 | h535
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h536 | h536
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h537 | h537
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h538 | h538
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h539 | h539
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
                                          · linarith only [h429, h540, hlam]
                                          · linarith only [h533, h540, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi1]
                                        · linarith only [h512, h539, hc02, hlam]
                                      · linarith only [h504, h538, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                                    · linarith only [h537, hlam, p437_0]
                                  · linarith only [h435, h536, hlam, p0_1]
                                · linarith only [h433, h535, hlam, p0_1]
                              · linarith only [h534, hlam, p0_0]
                            · linarith only [h504, h533, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi0]
                · linarith only [h503, hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h551 | h551
                · rcases p437_3 (m.d 1 2) (by simp) with h552 | h552
                  · linarith only [h429, h552, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p437_1]
                  · rcases p437_3 (m.d 2 3) (by simp) with h554 | h554
                    · linarith only [h552, h554, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                    · rcases p437_3 (m.d 2 4) (by simp) with h556 | h556
                      · linarith only [h556, hlam, p437_0]
                      · rcases p437_3 (m.d 2 5) (by simp) with h558 | h558
                        · linarith only [h552, h558, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
                        · rcases h2emax with h560 | h560 | h560 | h560 | h560
                          · linarith only [h552, h560, hlam, ht12, p437_1, u1ehi1]
                          · linarith only [h560, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h563 | h563
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h564 | h564
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h565 | h565
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h566 | h566
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h567 | h567
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h568 | h568
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h569 | h569
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
                                          · linarith only [h429, h570, hlam]
                                          · linarith only [h560, h570, hlam, ht12, u1ehi1]
                                        · linarith only [h558, h569, hlam, p437_1]
                                      · linarith only [h568, hlam, p437_0]
                                    · linarith only [h552, h560, h567, hlam, ht12, p437_1, u1ehi1]
                                  · linarith only [h435, h566, hlam, p0_1]
                                · linarith only [h433, h565, hlam, p0_1]
                              · linarith only [h564, hlam, p0_0]
                            · linarith only [h552, h563, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi0]
                          · linarith only [h552, h560, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h581 | h581
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h582 | h582
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h583 | h583
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h584 | h584
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h585 | h585
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h586 | h586
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h587 | h587
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                                          · linarith only [h429, h588, hlam]
                                          · linarith only [h554, h581, h588, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi1]
                                        · linarith only [h560, h587, hc02, hlam]
                                      · linarith only [h586, hlam, p437_0]
                                    · linarith only [h552, h585, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                                  · linarith only [h435, h584, hlam, p0_1]
                                · linarith only [h433, h583, hlam, p0_1]
                              · linarith only [h582, hlam, p0_0]
                            · linarith only [h552, h581, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi0]
                · linarith only [h551, hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h599 | h599
                · rcases p437_3 (m.d 1 2) (by simp) with h600 | h600
                  · linarith only [h429, h600, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p437_1]
                  · rcases p437_3 (m.d 2 3) (by simp) with h602 | h602
                    · linarith only [h600, h602, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                    · rcases p437_3 (m.d 2 4) (by simp) with h604 | h604
                      · linarith only [h600, h604, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                      · rcases p437_3 (m.d 2 5) (by simp) with h606 | h606
                        · linarith only [h606, hlam, p437_0]
                        · rcases h2emax with h608 | h608 | h608 | h608 | h608
                          · linarith only [h600, h608, hlam, ht12, p437_1, u1ehi1]
                          · linarith only [h608, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h611 | h611
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h612 | h612
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h613 | h613
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h614 | h614
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h615 | h615
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h616 | h616
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h617 | h617
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
                                          · linarith only [h429, h618, hlam]
                                          · linarith only [h608, h618, hlam, ht12, u1ehi1]
                                        · linarith only [h617, hlam, p437_0]
                                      · linarith only [h604, h616, hlam, p437_1]
                                    · linarith only [h600, h608, h615, hlam, ht12, p437_1, u1ehi1]
                                  · linarith only [h435, h614, hlam, p0_1]
                                · linarith only [h433, h613, hlam, p0_1]
                              · linarith only [h612, hlam, p0_0]
                            · linarith only [h600, h611, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h628 | h628
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h629 | h629
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h630 | h630
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h631 | h631
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h632 | h632
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h633 | h633
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h634 | h634
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                                          · linarith only [h429, h635, hlam]
                                          · linarith only [h602, h628, h635, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi1]
                                        · linarith only [h634, hlam, p437_0]
                                      · linarith only [h608, h633, hc02, hlam]
                                    · linarith only [h600, h632, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                                  · linarith only [h435, h631, hlam, p0_1]
                                · linarith only [h433, h630, hlam, p0_1]
                              · linarith only [h629, hlam, p0_0]
                            · linarith only [h600, h628, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p437_1, u1ehi0]
                          · linarith only [h600, h608, hlam, ht12, u1ehi1]
                · linarith only [h599, hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [h429, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [h429, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p437_1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [h429, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p437_1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [h429, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p437_1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h652 | h652
                · linarith only [h652, hlam, p437_0]
                · rcases p437_3 (m.d 1 2) (by simp) with h654 | h654
                  · linarith only [h429, h654, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h654, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hc23, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h659 | h659
                · rcases p437_3 (m.d 1 2) (by simp) with h660 | h660
                  · linarith only [h429, h660, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h660, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                · rcases p437_3 (m.d 1 2) (by simp) with h663 | h663
                  · linarith only [h429, h659, h663, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h663, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h666 | h666
                · rcases p437_3 (m.d 1 2) (by simp) with h667 | h667
                  · linarith only [h429, h667, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p437_1]
                  · linarith only [h667, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
                · rcases p437_3 (m.d 1 2) (by simp) with h670 | h670
                  · linarith only [h429, h666, h670, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h670, hc23, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h673 | h673
                · linarith only [h673, hlam, p437_0]
                · rcases p437_3 (m.d 1 2) (by simp) with h675 | h675
                  · linarith only [h429, h675, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h675, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hc24, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h679 | h679
                · rcases p437_3 (m.d 1 2) (by simp) with h680 | h680
                  · linarith only [h429, h680, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h680, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                · rcases p437_3 (m.d 1 2) (by simp) with h683 | h683
                  · linarith only [h429, h679, h683, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h683, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hlam, p437_0]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h687 | h687
                · rcases p437_3 (m.d 1 2) (by simp) with h688 | h688
                  · linarith only [h429, h688, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p437_1]
                  · linarith only [h688, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
                · rcases p437_3 (m.d 1 2) (by simp) with h691 | h691
                  · linarith only [h429, h687, h691, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h691, hc24, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h694 | h694
                · linarith only [h694, hlam, p437_0]
                · rcases p437_3 (m.d 1 2) (by simp) with h696 | h696
                  · linarith only [h429, h696, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h696, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hc25, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h700 | h700
                · rcases p437_3 (m.d 1 2) (by simp) with h701 | h701
                  · linarith only [h429, h701, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h701, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
                · rcases p437_3 (m.d 1 2) (by simp) with h704 | h704
                  · linarith only [h429, h700, h704, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h704, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                rcases p437_3 (m.d 0 2) (by simp) with h707 | h707
                · rcases p437_3 (m.d 1 2) (by simp) with h708 | h708
                  · linarith only [h429, h708, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h708, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
                · rcases p437_3 (m.d 1 2) (by simp) with h711 | h711
                  · linarith only [h429, h707, h711, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p437_1]
                  · linarith only [h711, hc25, hlam, hphi, ht12, p437_1, u1ehi1]
              · obtain ⟨p437_0, p437_1, p437_2, p437_3⟩ := h437c
                linarith only [hlam, p437_0]
    · linarith only [h428, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h716 | h716
    · rcases p0_3 (m.d 1 2) (by simp) with h717 | h717
      · linarith only [h717, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h719 | h719
        · linarith only [h719, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h721 | h721
          · linarith only [h721, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h723 | h723
            · linarith only [h723, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases h2bigk with h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h727 | h727
                · rcases p725_3 (m.d 1 2) (by simp) with h728 | h728
                  · linarith only [h728, hlam, p725_0]
                  · rcases p725_3 (m.d 2 3) (by simp) with h730 | h730
                    · linarith only [h730, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                    · rcases p725_3 (m.d 2 4) (by simp) with h732 | h732
                      · linarith only [h732, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                      · rcases p725_3 (m.d 2 5) (by simp) with h734 | h734
                        · linarith only [h734, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
                        · rcases h2emax with h736 | h736 | h736 | h736 | h736
                          · linarith only [h736, hlam, ht12, p725_1, u1ehi1]
                          · linarith only [h736, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h739 | h739
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h740 | h740
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h741 | h741
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h742 | h742
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h743 | h743
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h744 | h744
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h745 | h745
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h746 | h746
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h747 | h747
                                            · linarith only [h717, h747, hlam]
                                            · linarith only [h732, h747, hlam]
                                          · linarith only [h730, h746, hlam]
                                        · linarith only [h734, h745, hlam, p725_1]
                                      · linarith only [h732, h744, hlam, p725_1]
                                    · linarith only [h743, hc12, hc23, hlam, hphi, p725_1]
                                  · linarith only [h723, h739, h742, hc14, hlam, hphi, p725_1, u1ehi1]
                                · linarith only [h741, hlam, p0_0]
                              · linarith only [h739, h740, hc13, hlam, hphi, p725_1, u1ehi1]
                            · linarith only [h739, hlam, p725_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h758 | h758
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h759 | h759
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h760 | h760
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h761 | h761
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h762 | h762
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h763 | h763
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h764 | h764
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h765 | h765
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
                                            · linarith only [h717, h766, hlam]
                                            · linarith only [h732, h766, hlam]
                                          · linarith only [h730, h765, hlam]
                                        · linarith only [h734, h764, hlam, p725_1]
                                      · linarith only [h736, h763, hc02, hlam]
                                    · linarith only [h762, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                                  · linarith only [h723, h758, h761, hc14, hlam, hphi, p725_1, u1ehi1]
                                · linarith only [h760, hlam, p0_0]
                              · linarith only [h758, h759, hc13, hlam, hphi, p725_1, u1ehi1]
                            · linarith only [h758, hlam, p725_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h777 | h777
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h778 | h778
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h779 | h779
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h780 | h780
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h781 | h781
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h782 | h782
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
                                            · linarith only [h717, h785, hlam]
                                            · linarith only [h732, h785, hlam]
                                          · linarith only [h730, h784, hlam]
                                        · linarith only [h783, hc12, hc25, hlam, hphi, p725_1]
                                      · linarith only [h782, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                                    · linarith only [h781, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                                  · linarith only [h723, h780, hlam, p0_1]
                                · linarith only [h779, hlam, p0_0]
                              · linarith only [h777, h778, hc13, hlam, hphi, p725_1, u1ehi1]
                            · linarith only [h777, hlam, p725_0]
                · linarith only [h727, hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h797 | h797
                · rcases p725_3 (m.d 1 2) (by simp) with h798 | h798
                  · linarith only [h717, h798, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p725_1]
                  · rcases p725_3 (m.d 2 3) (by simp) with h800 | h800
                    · linarith only [h800, hlam, p725_0]
                    · rcases p725_3 (m.d 2 4) (by simp) with h802 | h802
                      · linarith only [h798, h802, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                      · rcases p725_3 (m.d 2 5) (by simp) with h804 | h804
                        · linarith only [h798, h804, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
                        · rcases h2emax with h806 | h806 | h806 | h806 | h806
                          · linarith only [h798, h806, hlam, ht12, p725_1, u1ehi1]
                          · linarith only [h806, hlam, ht12, u1ehi1]
                          · linarith only [h798, h806, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h810 | h810
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h811 | h811
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h812 | h812
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h813 | h813
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h814 | h814
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h815 | h815
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h816 | h816
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h817 | h817
                                          · linarith only [h798, h817, hlam]
                                          · linarith only [h810, h817, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi1]
                                        · linarith only [h804, h816, hlam, p725_1]
                                      · linarith only [h806, h815, hc02, hlam]
                                    · linarith only [h814, hlam, p725_0]
                                  · linarith only [h723, h813, hlam, p0_1]
                                · linarith only [h812, hlam, p0_0]
                              · linarith only [h719, h811, hlam, p0_1]
                            · linarith only [h798, h810, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h827 | h827
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h828 | h828
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h829 | h829
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h830 | h830
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h831 | h831
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h832 | h832
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h833 | h833
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
                                          · linarith only [h798, h834, hlam]
                                          · linarith only [h827, h834, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi1]
                                        · linarith only [h806, h833, hc02, hlam]
                                      · linarith only [h798, h832, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                                    · linarith only [h831, hlam, p725_0]
                                  · linarith only [h723, h830, hlam, p0_1]
                                · linarith only [h829, hlam, p0_0]
                              · linarith only [h719, h828, hlam, p0_1]
                            · linarith only [h798, h827, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi0]
                · linarith only [h797, hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h845 | h845
                · rcases p725_3 (m.d 1 2) (by simp) with h846 | h846
                  · linarith only [h717, h846, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p725_1]
                  · rcases p725_3 (m.d 2 3) (by simp) with h848 | h848
                    · linarith only [h846, h848, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                    · rcases p725_3 (m.d 2 4) (by simp) with h850 | h850
                      · linarith only [h850, hlam, p725_0]
                      · rcases p725_3 (m.d 2 5) (by simp) with h852 | h852
                        · linarith only [h846, h852, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
                        · rcases h2emax with h854 | h854 | h854 | h854 | h854
                          · linarith only [h846, h854, hlam, ht12, p725_1, u1ehi1]
                          · linarith only [h854, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h857 | h857
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h858 | h858
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h859 | h859
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h860 | h860
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h861 | h861
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h862 | h862
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h863 | h863
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h864 | h864
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h865 | h865
                                            · linarith only [h717, h865, hlam]
                                            · linarith only [h857, h864, h865, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi2]
                                          · linarith only [h848, h857, h864, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi1]
                                        · linarith only [h852, h863, hlam, p725_1]
                                      · linarith only [h862, hlam, p725_0]
                                    · linarith only [h854, h861, hc02, hlam]
                                  · linarith only [h723, h860, hlam, p0_1]
                                · linarith only [h859, hlam, p0_0]
                              · linarith only [h858, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h846, h857, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p725_1, u1ehi3]
                          · linarith only [h846, h854, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h877 | h877
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h878 | h878
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h879 | h879
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h880 | h880
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h881 | h881
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h882 | h882
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h883 | h883
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h884 | h884
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h885 | h885
                                            · linarith only [h717, h885, hlam]
                                            · linarith only [h877, h884, h885, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi2]
                                          · linarith only [h848, h877, h884, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi1]
                                        · linarith only [h854, h883, hc02, hlam]
                                      · linarith only [h882, hlam, p725_0]
                                    · linarith only [h846, h881, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                                  · linarith only [h723, h880, hlam, p0_1]
                                · linarith only [h879, hlam, p0_0]
                              · linarith only [h878, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h723, h846, h877, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p725_1, u1ehi4]
                · linarith only [h845, hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h897 | h897
                · rcases p725_3 (m.d 1 2) (by simp) with h898 | h898
                  · linarith only [h717, h898, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p725_1]
                  · rcases p725_3 (m.d 2 3) (by simp) with h900 | h900
                    · linarith only [h898, h900, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                    · rcases p725_3 (m.d 2 4) (by simp) with h902 | h902
                      · linarith only [h898, h902, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                      · rcases p725_3 (m.d 2 5) (by simp) with h904 | h904
                        · linarith only [h904, hlam, p725_0]
                        · rcases h2emax with h906 | h906 | h906 | h906 | h906
                          · linarith only [h898, h906, hlam, ht12, p725_1, u1ehi1]
                          · linarith only [h906, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h909 | h909
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h910 | h910
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h911 | h911
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h912 | h912
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h913 | h913
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h914 | h914
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h915 | h915
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h916 | h916
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h917 | h917
                                            · linarith only [h717, h917, hlam]
                                            · linarith only [h902, h909, h916, h917, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi2]
                                          · linarith only [h900, h909, h916, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi1]
                                        · linarith only [h915, hlam, p725_0]
                                      · linarith only [h902, h914, hlam, p725_1]
                                    · linarith only [h906, h913, hc02, hlam]
                                  · linarith only [h723, h912, hlam, p0_1]
                                · linarith only [h911, hlam, p0_0]
                              · linarith only [h910, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h717, h909, hlam, p0_1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h928 | h928
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h929 | h929
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h930 | h930
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h931 | h931
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h932 | h932
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h933 | h933
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h934 | h934
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h935 | h935
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h936 | h936
                                            · linarith only [h717, h936, hlam]
                                            · linarith only [h902, h928, h935, h936, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi2]
                                          · linarith only [h900, h928, h935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p725_1, u1ehi1]
                                        · linarith only [h934, hlam, p725_0]
                                      · linarith only [h906, h933, hc02, hlam]
                                    · linarith only [h898, h932, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                                  · linarith only [h723, h931, hlam, p0_1]
                                · linarith only [h930, hlam, p0_0]
                              · linarith only [h929, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h898, h928, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p725_1, u1ehi3]
                          · linarith only [h898, h906, hlam, ht12, u1ehi1]
                · linarith only [h897, hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [h717, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [h717, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p725_1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [h717, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p725_1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [h717, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p725_1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h954 | h954
                · linarith only [h954, hlam, p725_0]
                · rcases p725_3 (m.d 1 2) (by simp) with h956 | h956
                  · linarith only [h717, h956, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h956, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hc23, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h961 | h961
                · rcases p725_3 (m.d 1 2) (by simp) with h962 | h962
                  · linarith only [h717, h962, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h962, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                · rcases p725_3 (m.d 1 2) (by simp) with h965 | h965
                  · linarith only [h717, h961, h965, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h965, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h968 | h968
                · rcases p725_3 (m.d 1 2) (by simp) with h969 | h969
                  · linarith only [h717, h969, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p725_1]
                  · linarith only [h969, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
                · rcases p725_3 (m.d 1 2) (by simp) with h972 | h972
                  · linarith only [h717, h968, h972, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h972, hc23, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h975 | h975
                · linarith only [h975, hlam, p725_0]
                · rcases p725_3 (m.d 1 2) (by simp) with h977 | h977
                  · linarith only [h717, h977, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h977, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hc24, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h981 | h981
                · rcases p725_3 (m.d 1 2) (by simp) with h982 | h982
                  · linarith only [h717, h982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h982, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                · rcases p725_3 (m.d 1 2) (by simp) with h985 | h985
                  · linarith only [h717, h981, h985, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h985, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hlam, p725_0]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h989 | h989
                · rcases p725_3 (m.d 1 2) (by simp) with h990 | h990
                  · linarith only [h717, h990, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p725_1]
                  · linarith only [h990, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
                · rcases p725_3 (m.d 1 2) (by simp) with h993 | h993
                  · linarith only [h717, h989, h993, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h993, hc24, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h996 | h996
                · linarith only [h996, hlam, p725_0]
                · rcases p725_3 (m.d 1 2) (by simp) with h998 | h998
                  · linarith only [h717, h998, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h998, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hc25, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h1002 | h1002
                · rcases p725_3 (m.d 1 2) (by simp) with h1003 | h1003
                  · linarith only [h1003, h717, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h1003, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
                · rcases p725_3 (m.d 1 2) (by simp) with h1006 | h1006
                  · linarith only [h1002, h1006, h717, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h1006, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                rcases p725_3 (m.d 0 2) (by simp) with h1009 | h1009
                · rcases p725_3 (m.d 1 2) (by simp) with h1010 | h1010
                  · linarith only [h1010, h717, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h1010, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
                · rcases p725_3 (m.d 1 2) (by simp) with h1013 | h1013
                  · linarith only [h1009, h1013, h717, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p725_1]
                  · linarith only [h1013, hc25, hlam, hphi, ht12, p725_1, u1ehi1]
              · obtain ⟨p725_0, p725_1, p725_2, p725_3⟩ := h725c
                linarith only [hlam, p725_0]
    · linarith only [h716, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h1018 | h1018
    · rcases p0_3 (m.d 1 2) (by simp) with h1019 | h1019
      · linarith only [h1019, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h1021 | h1021
        · linarith only [h1021, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h1023 | h1023
          · linarith only [h1023, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h1025 | h1025
            · linarith only [h1025, hlam, p0_0]
            · rcases h2bigk with h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1029 | h1029
                · rcases p1027_3 (m.d 1 2) (by simp) with h1030 | h1030
                  · linarith only [h1030, hlam, p1027_0]
                  · rcases p1027_3 (m.d 2 3) (by simp) with h1032 | h1032
                    · linarith only [h1032, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                    · rcases p1027_3 (m.d 2 4) (by simp) with h1034 | h1034
                      · linarith only [h1034, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                      · rcases p1027_3 (m.d 2 5) (by simp) with h1036 | h1036
                        · linarith only [h1036, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
                        · rcases h2emax with h1038 | h1038 | h1038 | h1038 | h1038
                          · linarith only [h1038, hlam, ht12, p1027_1, u1ehi1]
                          · linarith only [h1038, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1041 | h1041
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1042 | h1042
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1043 | h1043
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1044 | h1044
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1045 | h1045
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1046 | h1046
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1047 | h1047
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1048 | h1048
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1049 | h1049
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1050 | h1050
                                              · linarith only [h1019, h1050, hlam]
                                              · linarith only [h1036, h1050, hlam]
                                            · linarith only [h1034, h1049, hlam]
                                          · linarith only [h1032, h1048, hlam]
                                        · linarith only [h1036, h1047, hlam, p1027_1]
                                      · linarith only [h1046, hc12, hc24, hlam, hphi, p1027_1]
                                    · linarith only [h1045, hc12, hc23, hlam, hphi, p1027_1]
                                  · linarith only [h1044, hlam, p0_0]
                                · linarith only [h1041, h1043, hc14, hlam, hphi, p1027_1, u1ehi1]
                              · linarith only [h1041, h1042, hc13, hlam, hphi, p1027_1, u1ehi1]
                            · linarith only [h1041, hlam, p1027_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1062 | h1062
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1063 | h1063
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1064 | h1064
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1065 | h1065
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1066 | h1066
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1067 | h1067
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1068 | h1068
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1069 | h1069
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1070 | h1070
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1071 | h1071
                                              · linarith only [h1019, h1071, hlam]
                                              · linarith only [h1036, h1071, hlam]
                                            · linarith only [h1034, h1070, hlam]
                                          · linarith only [h1032, h1069, hlam]
                                        · linarith only [h1036, h1068, hlam, p1027_1]
                                      · linarith only [h1067, hc12, hc24, hlam, hphi, p1027_1]
                                    · linarith only [h1066, hc12, hc23, hlam, hphi, p1027_1]
                                  · linarith only [h1065, hlam, p0_0]
                                · linarith only [h1062, h1064, hc14, hlam, hphi, p1027_1, u1ehi1]
                              · linarith only [h1062, h1063, hc13, hlam, hphi, p1027_1, u1ehi1]
                            · linarith only [h1062, hlam, p1027_0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1083 | h1083
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1084 | h1084
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1085 | h1085
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1086 | h1086
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1087 | h1087
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1088 | h1088
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1089 | h1089
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1090 | h1090
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1091 | h1091
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                                              · linarith only [h1019, h1092, hlam]
                                              · linarith only [h1036, h1092, hlam]
                                            · linarith only [h1034, h1091, hlam]
                                          · linarith only [h1032, h1090, hlam]
                                        · linarith only [h1038, h1089, hc02, hlam]
                                      · linarith only [h1088, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                                    · linarith only [h1087, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                                  · linarith only [h1086, hlam, p0_0]
                                · linarith only [h1085, hc14, hlam, hphi, p0_1, u1ehi4]
                              · linarith only [h1023, h1084, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h1083, hlam, p1027_0]
                · linarith only [h1029, hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1105 | h1105
                · rcases p1027_3 (m.d 1 2) (by simp) with h1106 | h1106
                  · linarith only [h1019, h1106, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1027_1]
                  · rcases p1027_3 (m.d 2 3) (by simp) with h1108 | h1108
                    · linarith only [h1108, hlam, p1027_0]
                    · rcases p1027_3 (m.d 2 4) (by simp) with h1110 | h1110
                      · linarith only [h1106, h1110, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                      · rcases p1027_3 (m.d 2 5) (by simp) with h1112 | h1112
                        · linarith only [h1106, h1112, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
                        · rcases h2emax with h1114 | h1114 | h1114 | h1114 | h1114
                          · linarith only [h1106, h1114, hlam, ht12, p1027_1, u1ehi1]
                          · linarith only [h1114, hlam, ht12, u1ehi1]
                          · linarith only [h1106, h1114, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1118 | h1118
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1119 | h1119
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1120 | h1120
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1121 | h1121
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1122 | h1122
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1123 | h1123
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1124 | h1124
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1125 | h1125
                                          · linarith only [h1106, h1125, hlam]
                                          · linarith only [h1118, h1125, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi1]
                                        · linarith only [h1112, h1124, hlam, p1027_1]
                                      · linarith only [h1114, h1123, hc02, hlam]
                                    · linarith only [h1122, hlam, p1027_0]
                                  · linarith only [h1121, hlam, p0_0]
                                · linarith only [h1023, h1120, hlam, p0_1]
                              · linarith only [h1021, h1119, hlam, p0_1]
                            · linarith only [h1106, h1118, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi0]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1135 | h1135
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1136 | h1136
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1137 | h1137
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1138 | h1138
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1139 | h1139
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1140 | h1140
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1141 | h1141
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1142 | h1142
                                          · linarith only [h1106, h1142, hlam]
                                          · linarith only [h1135, h1142, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi1]
                                        · linarith only [h1114, h1141, hc02, hlam]
                                      · linarith only [h1106, h1140, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                                    · linarith only [h1139, hlam, p1027_0]
                                  · linarith only [h1138, hlam, p0_0]
                                · linarith only [h1023, h1137, hlam, p0_1]
                              · linarith only [h1021, h1136, hlam, p0_1]
                            · linarith only [h1106, h1135, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi0]
                · linarith only [h1105, hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1153 | h1153
                · rcases p1027_3 (m.d 1 2) (by simp) with h1154 | h1154
                  · linarith only [h1019, h1154, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p1027_1]
                  · rcases p1027_3 (m.d 2 3) (by simp) with h1156 | h1156
                    · linarith only [h1154, h1156, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                    · rcases p1027_3 (m.d 2 4) (by simp) with h1158 | h1158
                      · linarith only [h1158, hlam, p1027_0]
                      · rcases p1027_3 (m.d 2 5) (by simp) with h1160 | h1160
                        · linarith only [h1154, h1160, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
                        · rcases h2emax with h1162 | h1162 | h1162 | h1162 | h1162
                          · linarith only [h1154, h1162, hlam, ht12, p1027_1, u1ehi1]
                          · linarith only [h1162, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1165 | h1165
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1166 | h1166
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1167 | h1167
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1168 | h1168
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1169 | h1169
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1170 | h1170
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1171 | h1171
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1172 | h1172
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1173 | h1173
                                            · linarith only [h1154, h1173, hlam]
                                            · linarith only [h1165, h1172, h1173, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi2]
                                          · linarith only [h1156, h1165, h1172, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi1]
                                        · linarith only [h1160, h1171, hlam, p1027_1]
                                      · linarith only [h1170, hlam, p1027_0]
                                    · linarith only [h1162, h1169, hc02, hlam]
                                  · linarith only [h1168, hlam, p0_0]
                                · linarith only [h1023, h1167, hlam, p0_1]
                              · linarith only [h1023, h1166, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h1023, h1154, h1165, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p1027_1, u1ehi3]
                          · linarith only [h1154, h1162, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1185 | h1185
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1186 | h1186
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1187 | h1187
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1188 | h1188
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1189 | h1189
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1190 | h1190
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1191 | h1191
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1192 | h1192
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1193 | h1193
                                            · linarith only [h1154, h1193, hlam]
                                            · linarith only [h1185, h1192, h1193, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi2]
                                          · linarith only [h1156, h1185, h1192, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi1]
                                        · linarith only [h1162, h1191, hc02, hlam]
                                      · linarith only [h1190, hlam, p1027_0]
                                    · linarith only [h1154, h1189, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                                  · linarith only [h1188, hlam, p0_0]
                                · linarith only [h1187, hc14, hlam, hphi, p0_1, u1ehi4]
                              · linarith only [h1154, h1185, h1186, hc13, hlam, hphi, p1027_1, u1ehi1]
                            · linarith only [h1154, h1185, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi0]
                · linarith only [h1153, hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1205 | h1205
                · rcases p1027_3 (m.d 1 2) (by simp) with h1206 | h1206
                  · linarith only [h1019, h1206, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1027_1]
                  · rcases p1027_3 (m.d 2 3) (by simp) with h1208 | h1208
                    · linarith only [h1206, h1208, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                    · rcases p1027_3 (m.d 2 4) (by simp) with h1210 | h1210
                      · linarith only [h1206, h1210, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                      · rcases p1027_3 (m.d 2 5) (by simp) with h1212 | h1212
                        · linarith only [h1212, hlam, p1027_0]
                        · rcases h2emax with h1214 | h1214 | h1214 | h1214 | h1214
                          · linarith only [h1206, h1214, hlam, ht12, p1027_1, u1ehi1]
                          · linarith only [h1214, hlam, ht12, u1ehi1]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1217 | h1217
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1218 | h1218
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1219 | h1219
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1220 | h1220
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1221 | h1221
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1222 | h1222
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1223 | h1223
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1224 | h1224
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1225 | h1225
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1226 | h1226
                                              · linarith only [h1019, h1226, hlam]
                                              · linarith only [h1224, h1226, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi2]
                                            · linarith only [h1210, h1217, h1224, h1225, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi2]
                                          · linarith only [h1208, h1217, h1224, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi1]
                                        · linarith only [h1223, hlam, p1027_0]
                                      · linarith only [h1210, h1222, hlam, p1027_1]
                                    · linarith only [h1214, h1221, hc02, hlam]
                                  · linarith only [h1220, hlam, p0_0]
                                · linarith only [h1219, hc14, hlam, hphi, p0_1, u1ehi4]
                              · linarith only [h1023, h1218, hc13, hlam, hphi, p0_1, u1ehi3]
                            · linarith only [h1023, h1206, h1217, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, p1027_1, u1ehi3]
                          · rcases m.htr 0 1 2 (by decide) (by decide) with h1238 | h1238
                            · rcases m.htr 0 1 3 (by decide) (by decide) with h1239 | h1239
                              · rcases m.htr 0 1 4 (by decide) (by decide) with h1240 | h1240
                                · rcases m.htr 0 1 5 (by decide) (by decide) with h1241 | h1241
                                  · rcases m.htr 0 2 3 (by decide) (by decide) with h1242 | h1242
                                    · rcases m.htr 0 2 4 (by decide) (by decide) with h1243 | h1243
                                      · rcases m.htr 0 2 5 (by decide) (by decide) with h1244 | h1244
                                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1245 | h1245
                                          · rcases m.htr 1 2 4 (by decide) (by decide) with h1246 | h1246
                                            · rcases m.htr 1 2 5 (by decide) (by decide) with h1247 | h1247
                                              · linarith only [h1019, h1247, hlam]
                                              · linarith only [h1238, h1245, h1247, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi2]
                                            · linarith only [h1210, h1238, h1245, h1246, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi2]
                                          · linarith only [h1208, h1238, h1245, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi1]
                                        · linarith only [h1244, hlam, p1027_0]
                                      · linarith only [h1214, h1243, hc02, hlam]
                                    · linarith only [h1206, h1242, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                                  · linarith only [h1241, hlam, p0_0]
                                · linarith only [h1240, hc14, hlam, hphi, p0_1, u1ehi4]
                              · linarith only [h1206, h1238, h1239, hc13, hlam, hphi, p1027_1, u1ehi1]
                            · linarith only [h1206, h1238, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1027_1, u1ehi0]
                          · linarith only [h1206, h1214, hlam, ht12, u1ehi1]
                · linarith only [h1205, hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [h1019, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [h1019, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1027_1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [h1019, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p1027_1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [h1019, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1027_1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1266 | h1266
                · linarith only [h1266, hlam, p1027_0]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1268 | h1268
                  · linarith only [h1019, h1268, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1268, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1273 | h1273
                · rcases p1027_3 (m.d 1 2) (by simp) with h1274 | h1274
                  · linarith only [h1019, h1274, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1274, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1277 | h1277
                  · linarith only [h1019, h1273, h1277, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1277, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1280 | h1280
                · rcases p1027_3 (m.d 1 2) (by simp) with h1281 | h1281
                  · linarith only [h1019, h1281, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1027_1]
                  · linarith only [h1281, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1284 | h1284
                  · linarith only [h1019, h1280, h1284, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1284, hc23, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1287 | h1287
                · linarith only [h1287, hlam, p1027_0]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1289 | h1289
                  · linarith only [h1019, h1289, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1289, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1293 | h1293
                · rcases p1027_3 (m.d 1 2) (by simp) with h1294 | h1294
                  · linarith only [h1019, h1294, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1294, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1297 | h1297
                  · linarith only [h1019, h1293, h1297, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1297, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hlam, p1027_0]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1301 | h1301
                · rcases p1027_3 (m.d 1 2) (by simp) with h1302 | h1302
                  · linarith only [h1019, h1302, hc01, hc25, hlam, hphi, ht0b, ht5b, p0_1, p1027_1]
                  · linarith only [h1302, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1305 | h1305
                  · linarith only [h1019, h1301, h1305, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1305, hc24, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1308 | h1308
                · linarith only [h1308, hlam, p1027_0]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1310 | h1310
                  · linarith only [h1019, h1310, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1310, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1314 | h1314
                · rcases p1027_3 (m.d 1 2) (by simp) with h1315 | h1315
                  · linarith only [h1019, h1315, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1315, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1318 | h1318
                  · linarith only [h1019, h1314, h1318, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1318, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                rcases p1027_3 (m.d 0 2) (by simp) with h1321 | h1321
                · rcases p1027_3 (m.d 1 2) (by simp) with h1322 | h1322
                  · linarith only [h1019, h1322, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1322, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
                · rcases p1027_3 (m.d 1 2) (by simp) with h1325 | h1325
                  · linarith only [h1019, h1321, h1325, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, p1027_1]
                  · linarith only [h1325, hc25, hlam, hphi, ht12, p1027_1, u1ehi1]
              · obtain ⟨p1027_0, p1027_1, p1027_2, p1027_3⟩ := h1027c
                linarith only [hlam, p1027_0]
    · linarith only [h1018, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_R_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                                      · linarith only [h0, h12, h17, h21, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                      · rcases h1bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h16, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h0, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h12, h14, h15, h17, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h0, h14, h15, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h1, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h9, hlam, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h14, h15, h17, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h0, h11, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h2, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h10, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h12, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h11, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h3, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h11, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h13, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h14, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                  · linarith only [h0, h13, h15, h16, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                                  · linarith only [h0, h12, h15, h50, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                                      · rcases h1bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h10, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h13, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, h10, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, h13, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h1, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h9, hlam, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h10, h52, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, h13, h50, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h2, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h10, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h13, h50, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h3, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h11, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h13, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h14, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                      · linarith only [h0, h15, h5, h52, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                                      · linarith only [h0, h12, h15, h52, h81, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                      · linarith only [h0, h12, h14, h15, h81, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                                    · linarith only [h0, h10, h14, h86, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                                      · linarith only [h10, h14, h84, h88, hlam]
                                      · rcases h1bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h85, h88, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          rcases p90_3 (m.d 0 1) (by simp) with h94 | h94
                                          · rcases p90_3 (m.d 1 2) (by simp) with h95 | h95
                                            · linarith only [h0, h95, hlam]
                                            · linarith only [h10, h95, hlam]
                                          · linarith only [h94, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          rcases p90_3 (m.d 0 1) (by simp) with h99 | h99
                                          · rcases p90_3 (m.d 1 2) (by simp) with h100 | h100
                                            · linarith only [h0, h100, hlam]
                                            · linarith only [h100, h11, hlam]
                                          · linarith only [h99, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h0, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h85, h88, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h0, h10, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h0, h10, h14, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h1, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h9, hlam, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h1, h10, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h0, h10, h14, h84, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h2, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h10, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h12, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h14, hlam, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h3, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h11, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h13, hlam, p90_0]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [h10, h3, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                                        · obtain ⟨p90_0, p90_1, p90_2, p90_3⟩ := h90c
                                          linarith only [hlam, p90_0]
                                  · linarith only [h0, h13, h84, h85, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                                  · linarith only [h0, h12, h125, h14, h4, h7, h8, h84, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                                    · linarith only [h0, h12, h127, h14, h5, h84, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                                      · linarith only [h12, h129, h14, hlam]
                                      · rcases h1bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h12, h84, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h12, h84, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h129, h13, h84, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h0, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h129, h13, h84, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h0, h12, h84, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h1, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h9, hlam, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h12, h84, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h0, h11, h127, h84, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h2, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h10, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h12, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h14, hlam, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h3, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h11, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h13, hlam, p131_0]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [h12, h84, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p131_1]
                                        · obtain ⟨p131_0, p131_1, p131_2, p131_3⟩ := h131c
                                          linarith only [hlam, p131_0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h12, h13, h157, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                                  · linarith only [h13, h160, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                                    · linarith only [h0, h10, h157, h162, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                                      · linarith only [h12, h13, h157, h164, hlam]
                                      · rcases h1bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h159, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h159, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          rcases p166_3 (m.d 0 1) (by simp) with h170 | h170
                                          · rcases p166_3 (m.d 1 2) (by simp) with h171 | h171
                                            · linarith only [h0, h171, hlam]
                                            · linarith only [h10, h171, hlam]
                                          · linarith only [h170, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h13, h159, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h0, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h159, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h0, h13, h159, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h1, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h9, hlam, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h10, h13, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h13, hlam, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h2, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h10, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h12, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h157, hlam, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h3, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h11, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h10, h13, h164, hc24, hc45, hlam, hphi, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                · linarith only [h12, h13, h159, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                                · linarith only [h0, h12, h197, h199, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                                      · rcases h1bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h201, h203, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h201, h203, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h10, h199, h201, h203, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          rcases p204_3 (m.d 0 1) (by simp) with h209 | h209
                                          · rcases p204_3 (m.d 1 2) (by simp) with h210 | h210
                                            · linarith only [h0, h210, hlam]
                                            · linarith only [h11, h210, hlam]
                                          · linarith only [h209, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h0, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h201, h203, h9, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h0, h10, h199, h201, h203, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h1, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h9, hlam, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h12, hlam, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h11, h12, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h2, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h10, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h0, h12, h197, h203, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h3, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h11, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h197, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h198, hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [hlam, p204_0]
                                      · linarith only [h0, h12, h201, h203, h4, h7, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h12, h197, h198, h199, h201, h202, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h12, h197, h201, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h12, h197, h198, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                                · linarith only [h0, h12, h239, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                                  · linarith only [h197, h241, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                                      · rcases h1bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          rcases p245_3 (m.d 0 1) (by simp) with h248 | h248
                                          · rcases p245_3 (m.d 1 2) (by simp) with h249 | h249
                                            · linarith only [h0, h249, hlam]
                                            · linarith only [h249, h9, hlam]
                                          · linarith only [h248, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h10, h243, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          rcases p245_3 (m.d 0 1) (by simp) with h254 | h254
                                          · rcases p245_3 (m.d 1 2) (by simp) with h255 | h255
                                            · linarith only [h0, h255, hlam]
                                            · linarith only [h11, h255, hlam]
                                          · linarith only [h254, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, h10, h243, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, h197, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h1, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h9, hlam, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h12, hlam, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h197, hlam, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h2, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h10, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, h12, h197, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h3, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h11, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h238, hlam, p245_0]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [hlam, p245_0]
                                      · linarith only [h0, h10, h12, h243, h244, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                                      · rcases h1bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          rcases p281_3 (m.d 0 1) (by simp) with h284 | h284
                                          · rcases p281_3 (m.d 1 2) (by simp) with h285 | h285
                                            · linarith only [h0, h285, hlam]
                                            · linarith only [h285, h9, hlam]
                                          · linarith only [h284, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h238, h239, h243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h238, h239, h243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h0, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h0, h238, h239, h243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h0, h238, h239, h243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h1, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h9, hlam, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h12, hlam, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h197, hlam, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h2, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h10, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h12, h9, hc23, hc34, hlam, hphi, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h0, h12, h238, h239, h243, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h3, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h11, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h197, h9, hc23, hc35, hlam, hphi, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h238, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                      · linarith only [h12, h238, h280, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                                · linarith only [h12, h312, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h314 | h314
                                  · linarith only [h197, h314, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h316 | h316
                                    · linarith only [h10, h238, h316, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h318 | h318
                                      · rcases h1bigk with h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          rcases p319_3 (m.d 0 1) (by simp) with h322 | h322
                                          · rcases p319_3 (m.d 1 2) (by simp) with h323 | h323
                                            · linarith only [h0, h323, hlam]
                                            · linarith only [h323, h9, hlam]
                                          · linarith only [h322, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          rcases p319_3 (m.d 0 1) (by simp) with h327 | h327
                                          · rcases p319_3 (m.d 1 2) (by simp) with h328 | h328
                                            · linarith only [h0, h328, hlam]
                                            · linarith only [h10, h328, hlam]
                                          · linarith only [h327, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          rcases p319_3 (m.d 0 1) (by simp) with h332 | h332
                                          · rcases p319_3 (m.d 1 2) (by simp) with h333 | h333
                                            · linarith only [h0, h333, hlam]
                                            · linarith only [h11, h333, hlam]
                                          · linarith only [h332, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, h10, h238, h312, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h1, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h9, hlam, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h12, hlam, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h197, hlam, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h2, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h10, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h238, hlam, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h3, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h11, hlam, p319_0]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, h11, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, h238, h318, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [hlam, p319_0]
                                      · rcases h1bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          rcases p357_3 (m.d 0 1) (by simp) with h360 | h360
                                          · rcases p357_3 (m.d 1 2) (by simp) with h361 | h361
                                            · linarith only [h0, h361, hlam]
                                            · linarith only [h361, h9, hlam]
                                          · linarith only [h360, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          rcases p357_3 (m.d 0 1) (by simp) with h365 | h365
                                          · rcases p357_3 (m.d 1 2) (by simp) with h366 | h366
                                            · linarith only [h0, h366, hlam]
                                            · linarith only [h10, h366, hlam]
                                          · linarith only [h365, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          rcases p357_3 (m.d 0 1) (by simp) with h370 | h370
                                          · rcases p357_3 (m.d 1 2) (by simp) with h371 | h371
                                            · linarith only [h0, h371, hlam]
                                            · linarith only [h11, h371, hlam]
                                          · linarith only [h370, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h0, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h0, h10, h312, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h1, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h9, hlam, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h12, hlam, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h197, hlam, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h2, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h10, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h238, hlam, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h3, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h11, hlam, p357_0]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [h0, h238, h4, h7, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h396 | h396
                            · linarith only [h11, h396, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
                              · linarith only [h10, h11, h398, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                                · linarith only [h0, h11, h400, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h11, h395, h400, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                            · linarith only [h10, h11, h395, h403, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                              · linarith only [h10, h11, h405, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                                · linarith only [h0, h11, h395, h407, h6, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                                  · linarith only [h11, h403, h409, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                                    · linarith only [h0, h10, h11, h411, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                                      · linarith only [h0, h10, h11, h4, h407, h411, h413, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                      · rcases h1bigk with h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h10, h407, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          rcases p415_3 (m.d 0 1) (by simp) with h418 | h418
                                          · rcases p415_3 (m.d 1 2) (by simp) with h419 | h419
                                            · linarith only [h0, h419, hlam]
                                            · linarith only [h419, h9, hlam]
                                          · linarith only [h418, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          rcases p415_3 (m.d 0 1) (by simp) with h423 | h423
                                          · rcases p415_3 (m.d 1 2) (by simp) with h424 | h424
                                            · linarith only [h0, h424, hlam]
                                            · linarith only [h10, h424, hlam]
                                          · linarith only [h423, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h10, h11, h407, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h0, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h11, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h0, h11, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h11, hlam, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h1, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h9, hlam, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h395, hlam, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h403, hlam, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h2, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h10, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h405, hlam, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h3, hlam, p415_0]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h0, h4, h403, h413, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h0, h4, h403, h413, h7, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [hlam, p415_0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                          · linarith only [h10, h450, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                                · linarith only [h0, h4, h450, h452, h454, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                                  · linarith only [h0, h10, h4, h454, h456, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h10, h4, h452, h454, h456, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h10, h452, h453, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h460 | h460
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h461 | h461
                                · linarith only [h0, h10, h461, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h463 | h463
                                  · linarith only [h0, h10, h4, h452, h461, h463, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h466 | h466
                                      · rcases h1bigk with h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h449, hc01, hc25, hlam, hphi, ht0b, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          rcases p467_3 (m.d 0 1) (by simp) with h470 | h470
                                          · rcases p467_3 (m.d 1 2) (by simp) with h471 | h471
                                            · linarith only [h0, h471, hlam]
                                            · linarith only [h471, h9, hlam]
                                          · linarith only [h470, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h10, h449, h463, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          rcases p467_3 (m.d 0 1) (by simp) with h476 | h476
                                          · rcases p467_3 (m.d 1 2) (by simp) with h477 | h477
                                            · linarith only [h0, h477, hlam]
                                            · linarith only [h449, h477, hlam]
                                          · linarith only [h476, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h10, hlam, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h461, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h1, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h9, hlam, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h450, hlam, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h452, hlam, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h2, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h461, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h461, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h449, h461, h463, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h3, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h449, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h460, hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                      · linarith only [h0, h10, h4, h449, h461, h463, h466, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h10, h449, h460, h463, h465, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h10, h449, h460, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                          · linarith only [h10, h504, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                            · linarith only [h449, h506, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h509 | h509
                                · linarith only [h449, h504, h509, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h511 | h511
                                  · linarith only [h449, h506, h511, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h514 | h514
                                      · rcases h1bigk with h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          rcases p515_3 (m.d 0 1) (by simp) with h518 | h518
                                          · rcases p515_3 (m.d 1 2) (by simp) with h519 | h519
                                            · linarith only [h0, h519, hlam]
                                            · linarith only [h519, h9, hlam]
                                          · linarith only [h518, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h449, h508, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h449, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h0, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h449, h513, h9, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h10, hlam, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h449, hlam, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h1, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h9, hlam, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h504, hlam, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h506, hlam, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h2, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h0, h10, h4, h509, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h0, h10, h4, h449, h509, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h3, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h9, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h0, h4, h449, h509, h513, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h508, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                      · linarith only [h10, h508, h509, h514, hlam]
                                    · linarith only [h10, h508, h513, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h547 | h547
                                · linarith only [h0, h10, h5, h547, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h549 | h549
                                  · linarith only [h0, h10, h5, h549, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h551 | h551
                                    · linarith only [h0, h10, h4, h508, h547, h551, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h0, h10, h4, h551, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h554 | h554
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h555 | h555
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h556 | h556
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h558 | h558
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                                    · linarith only [h0, h4, h554, h561, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h4, h554, h558, h561, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h555, h557, h560, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h4, h554, h558, h559, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h567 | h567
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h568 | h568
                                    · linarith only [h554, h558, h568, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                      · linarith only [h0, h4, h554, h558, h566, h570, h9, hc01, hc15, hlam, hphi, ht0b, ht5b]
                                      · rcases h1bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h555, h568, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h555, h566, h568, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          rcases p572_3 (m.d 0 1) (by simp) with h576 | h576
                                          · rcases p572_3 (m.d 1 2) (by simp) with h577 | h577
                                            · linarith only [h0, h577, hlam]
                                            · linarith only [h554, h577, hlam]
                                          · linarith only [h576, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          rcases p572_3 (m.d 0 1) (by simp) with h581 | h581
                                          · rcases p572_3 (m.d 1 2) (by simp) with h582 | h582
                                            · linarith only [h0, h582, hlam]
                                            · linarith only [h555, h582, hlam]
                                          · linarith only [h581, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h0, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h9, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h0, h4, h554, h558, h566, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h1, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h555, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h0, h4, h554, h566, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h0, h4, h554, h558, h566, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h2, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h554, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h556, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h558, hlam, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h3, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h555, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h557, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h3, h554, h566, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [hlam, p572_0]
                                  · linarith only [h557, h567, h9, hlam]
                                · linarith only [h0, h4, h554, h566, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h555, h557, h9, hlam]
                          · linarith only [h554, h556, h9, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                              · linarith only [h554, h555, h612, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h614 | h614
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h616 | h616
                                    · linarith only [h554, h555, h612, h615, h616, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                                      · linarith only [h554, h555, h614, h616, h618, hlam]
                                      · rcases h1bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h554, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h554, h555, h611, h614, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          rcases p620_3 (m.d 0 1) (by simp) with h624 | h624
                                          · rcases p620_3 (m.d 1 2) (by simp) with h625 | h625
                                            · linarith only [h0, h625, hlam]
                                            · linarith only [h554, h625, hlam]
                                          · linarith only [h624, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h554, h555, h614, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h0, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h9, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h0, h554, h614, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h555, hlam, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h1, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h0, h4, h554, h614, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h2, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h554, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h610, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h612, hlam, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h3, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h554, h614, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h611, hlam, p620_0]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [h0, h4, h554, h555, h614, h616, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [hlam, p620_0]
                                  · linarith only [h611, h615, h9, hlam]
                                · linarith only [h0, h4, h554, h614, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h652 | h652
                              · linarith only [h554, h555, h652, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h655 | h655
                                  · linarith only [h0, h4, h554, h611, h654, h655, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h657 | h657
                                    · linarith only [h0, h554, h652, h657, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h659 | h659
                                      · linarith only [h554, h654, h655, h657, h659, h9, hlam]
                                      · linarith only [h554, h654, h655, h659, h9, hc34, hc45, hlam, hphi]
                                · linarith only [h0, h4, h554, h654, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h554, h610, h9, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h670 | h670
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h671 | h671
                                      · rcases h1bigk with h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h664, h669, h671, hc01, hc45, hlam, hphi, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h665, h671, hc01, hc45, hlam, hphi, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h554, h664, h669, h671, hc01, hc45, hlam, hphi, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          rcases p672_3 (m.d 0 1) (by simp) with h677 | h677
                                          · rcases p672_3 (m.d 1 2) (by simp) with h678 | h678
                                            · linarith only [h0, h678, hlam]
                                            · linarith only [h664, h678, hlam]
                                          · linarith only [h677, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h0, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h9, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h554, hlam, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h554, h668, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h1, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h0, h4, h554, h664, h669, h671, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h0, h4, h664, h669, h671, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h2, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h664, h669, h671, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h665, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h0, h4, h554, h664, h668, h669, h671, hc01, hc45, hlam, hphi, ht0b, ht5b, p672_1]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h3, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h664, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h666, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [h667, hlam, p672_0]
                                        · obtain ⟨p672_0, p672_1, p672_2, p672_3⟩ := h672c
                                          linarith only [hlam, p672_0]
                                      · linarith only [h0, h4, h664, h670, h671, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h3, h554, h664, h667, h670, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h666, h669, h9, hlam]
                                · linarith only [h0, h4, h664, h668, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h554, h664, h667, hlam]
                            · linarith only [h664, h666, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h708 | h708
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                                · linarith only [h0, h4, h665, h708, h710, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h4, h664, h7, h710, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h554, h664, h709, hlam]
                            · linarith only [h664, h708, h9, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h715 | h715
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h718 | h718
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h719 | h719
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h720 | h720
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h721 | h721
                                      · rcases h1bigk with h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          rcases p722_3 (m.d 0 1) (by simp) with h724 | h724
                                          · rcases p722_3 (m.d 1 2) (by simp) with h725 | h725
                                            · linarith only [h725, hlam, p722_0]
                                            · rcases p722_3 (m.d 1 3) (by simp) with h727 | h727
                                              · linarith only [h1, h727, hlam]
                                              · linarith only [h727, h9, hlam]
                                          · linarith only [h724, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h715, h721, hc01, hc45, hlam, hphi, ht0b, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h715, h721, hc01, hc45, hlam, hphi, ht0b, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          rcases p722_3 (m.d 0 1) (by simp) with h733 | h733
                                          · rcases p722_3 (m.d 1 2) (by simp) with h734 | h734
                                            · linarith only [h0, h734, hlam]
                                            · rcases p722_3 (m.d 1 3) (by simp) with h736 | h736
                                              · linarith only [h1, h736, hlam]
                                              · linarith only [h716, h736, hlam]
                                          · linarith only [h733, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h0, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h9, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h554, hlam, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h664, hlam, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h1, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h9, hc12, hc23, hlam, hphi, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h0, h4, h715, h721, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h2, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h715, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h0, h4, h554, h664, h718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h3, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h716, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [h717, hlam, p722_0]
                                        · obtain ⟨p722_0, p722_1, p722_2, p722_3⟩ := h722c
                                          linarith only [hlam, p722_0]
                                      · rcases h1bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          rcases p760_3 (m.d 0 1) (by simp) with h762 | h762
                                          · rcases p760_3 (m.d 1 2) (by simp) with h763 | h763
                                            · linarith only [h763, hlam, p760_0]
                                            · rcases p760_3 (m.d 1 3) (by simp) with h765 | h765
                                              · linarith only [h1, h765, hlam]
                                              · linarith only [h765, h9, hlam]
                                          · linarith only [h762, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h717, hc01, hc45, hlam, hphi, ht0b, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h717, h721, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h0, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h9, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h554, hlam, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h664, hlam, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h1, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h0, h4, h717, h721, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h2, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h715, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h0, h4, h554, h664, h718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h3, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h716, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [h717, hlam, p760_0]
                                        · obtain ⟨p760_0, p760_1, p760_2, p760_3⟩ := h760c
                                          linarith only [hlam, p760_0]
                                    · linarith only [h554, h717, h720, hlam]
                                  · linarith only [h716, h719, h9, hlam]
                                · linarith only [h1, h715, h718, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h795 | h795
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h796 | h796
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h797 | h797
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
                                      · linarith only [h715, h717, h798, hlam]
                                      · rcases h1bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          rcases p800_3 (m.d 0 1) (by simp) with h802 | h802
                                          · rcases p800_3 (m.d 1 2) (by simp) with h803 | h803
                                            · linarith only [h803, hlam, p800_0]
                                            · rcases p800_3 (m.d 1 3) (by simp) with h805 | h805
                                              · linarith only [h1, h805, hlam]
                                              · linarith only [h805, h9, hlam]
                                          · linarith only [h802, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          rcases p800_3 (m.d 0 1) (by simp) with h810 | h810
                                          · rcases p800_3 (m.d 1 2) (by simp) with h811 | h811
                                            · linarith only [h0, h811, hlam]
                                            · rcases p800_3 (m.d 1 3) (by simp) with h813 | h813
                                              · linarith only [h1, h813, hlam]
                                              · linarith only [h715, h813, hlam]
                                          · linarith only [h810, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          rcases p800_3 (m.d 0 1) (by simp) with h817 | h817
                                          · rcases p800_3 (m.d 1 2) (by simp) with h818 | h818
                                            · linarith only [h0, h818, hlam]
                                            · rcases p800_3 (m.d 1 3) (by simp) with h820 | h820
                                              · linarith only [h1, h820, hlam]
                                              · linarith only [h716, h820, hlam]
                                          · linarith only [h817, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h0, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h9, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h554, hlam, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h664, hlam, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h1, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h4, h554, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h2, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h717, h797, hc12, hc24, hlam, hphi, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h715, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h717, hlam, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h3, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h716, hlam, p800_0]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [h0, h5, h717, h797, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p800_1]
                                        · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                          linarith only [hlam, p800_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h844 | h844
                                      · linarith only [h554, h797, h844, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          rcases p846_3 (m.d 0 1) (by simp) with h848 | h848
                                          · rcases p846_3 (m.d 1 2) (by simp) with h849 | h849
                                            · linarith only [h849, hlam, p846_0]
                                            · rcases p846_3 (m.d 1 3) (by simp) with h851 | h851
                                              · linarith only [h1, h851, hlam]
                                              · linarith only [h851, h9, hlam]
                                          · linarith only [h848, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          rcases p846_3 (m.d 0 1) (by simp) with h856 | h856
                                          · rcases p846_3 (m.d 1 2) (by simp) with h857 | h857
                                            · linarith only [h0, h857, hlam]
                                            · rcases p846_3 (m.d 1 3) (by simp) with h859 | h859
                                              · linarith only [h1, h859, hlam]
                                              · linarith only [h715, h859, hlam]
                                          · linarith only [h856, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          rcases p846_3 (m.d 0 1) (by simp) with h863 | h863
                                          · rcases p846_3 (m.d 1 2) (by simp) with h864 | h864
                                            · linarith only [h0, h864, hlam]
                                            · rcases p846_3 (m.d 1 3) (by simp) with h866 | h866
                                              · linarith only [h1, h866, hlam]
                                              · linarith only [h716, h866, hlam]
                                          · linarith only [h863, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h0, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h9, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h554, hlam, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h664, hlam, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h1, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h0, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h2, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h715, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h717, hlam, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h3, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h716, hlam, p846_0]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [h664, h797, hc14, hc45, hlam, hphi, p846_1]
                                        · obtain ⟨p846_0, p846_1, p846_2, p846_3⟩ := h846c
                                          linarith only [hlam, p846_0]
                                  · linarith only [h716, h796, h9, hlam]
                                · linarith only [h715, h795, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                              · linarith only [h715, h716, h892, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                                  · linarith only [h0, h4, h715, h716, h895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h897 | h897
                                    · linarith only [h554, h892, h894, h895, h897, hc12, hc35, hlam, hphi, ht23]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h899 | h899
                                      · linarith only [h554, h715, h897, h899, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          rcases p901_3 (m.d 0 1) (by simp) with h903 | h903
                                          · rcases p901_3 (m.d 1 2) (by simp) with h904 | h904
                                            · linarith only [h904, hlam, p901_0]
                                            · rcases p901_3 (m.d 1 3) (by simp) with h906 | h906
                                              · linarith only [h1, h906, hlam]
                                              · linarith only [h9, h906, hlam]
                                          · linarith only [h903, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          rcases p901_3 (m.d 0 1) (by simp) with h911 | h911
                                          · rcases p901_3 (m.d 1 2) (by simp) with h912 | h912
                                            · linarith only [h0, h912, hlam]
                                            · rcases p901_3 (m.d 1 3) (by simp) with h914 | h914
                                              · linarith only [h1, h914, hlam]
                                              · linarith only [h715, h914, hlam]
                                          · linarith only [h911, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h715, h716, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h0, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h9, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h554, hlam, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h664, hlam, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h1, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h0, h4, h554, h7, h8, h895, h899, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h716, hlam, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h2, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h715, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h892, hlam, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h3, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h0, h4, h664, h7, h8, h895, h899, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h0, h4, h664, h7, h8, h895, h899, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h0, h4, h664, h7, h8, h895, h899, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                · linarith only [h1, h715, h894, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h941 | h941
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h942 | h942
                                · linarith only [h0, h4, h715, h940, h942, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h944 | h944
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h945 | h945
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h946 | h946
                                      · rcases h1bigk with h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          rcases p947_3 (m.d 0 1) (by simp) with h949 | h949
                                          · rcases p947_3 (m.d 1 2) (by simp) with h950 | h950
                                            · linarith only [h950, hlam, p947_0]
                                            · rcases p947_3 (m.d 1 3) (by simp) with h952 | h952
                                              · linarith only [h1, h952, hlam]
                                              · linarith only [h9, h952, hlam]
                                          · linarith only [h949, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h940, h946, hc01, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h715, h940, h946, hc01, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          rcases p947_3 (m.d 0 1) (by simp) with h958 | h958
                                          · rcases p947_3 (m.d 1 2) (by simp) with h959 | h959
                                            · linarith only [h0, h959, hlam]
                                            · rcases p947_3 (m.d 1 3) (by simp) with h961 | h961
                                              · linarith only [h1, h961, hlam]
                                              · linarith only [h940, h961, hlam]
                                          · linarith only [h958, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h0, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h9, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h554, hlam, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h664, hlam, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h1, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h715, hlam, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h9, h942, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h2, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h554, hc12, hc24, hlam, hphi, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h0, h4, h7, h715, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h0, h4, h664, h7, h715, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h3, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p947_1]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h940, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [h941, hlam, p947_0]
                                        · obtain ⟨p947_0, p947_1, p947_2, p947_3⟩ := h947c
                                          linarith only [hlam, p947_0]
                                      · linarith only [h0, h4, h7, h8, h9, h942, h946, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                    · linarith only [h554, h9, h940, h941, h942, h945, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h9, h940, h944, hlam]
                              · linarith only [h715, h940, h941, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h989 | h989
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h990 | h990
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h992 | h992
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h993 | h993
                                      · rcases h1bigk with h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          rcases p994_3 (m.d 0 1) (by simp) with h996 | h996
                                          · rcases p994_3 (m.d 1 2) (by simp) with h997 | h997
                                            · linarith only [h997, hlam, p994_0]
                                            · rcases p994_3 (m.d 1 3) (by simp) with h999 | h999
                                              · linarith only [h1, h999, hlam]
                                              · linarith only [h9, h999, hlam]
                                          · linarith only [h996, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          rcases p994_3 (m.d 0 1) (by simp) with h1003 | h1003
                                          · rcases p994_3 (m.d 1 2) (by simp) with h1004 | h1004
                                            · linarith only [h0, h1004, hlam]
                                            · rcases p994_3 (m.d 1 3) (by simp) with h1006 | h1006
                                              · linarith only [h1006, hlam, p994_0]
                                              · rcases p994_3 (m.d 1 4) (by simp) with h1008 | h1008
                                                · linarith only [h1008, h2, hlam]
                                                · linarith only [h1008, h715, hlam]
                                          · linarith only [h1003, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h989, hc01, hc45, hlam, hphi, ht0b, ht5b, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          rcases p994_3 (m.d 0 1) (by simp) with h1013 | h1013
                                          · rcases p994_3 (m.d 1 2) (by simp) with h1014 | h1014
                                            · linarith only [h0, h1014, hlam]
                                            · rcases p994_3 (m.d 1 3) (by simp) with h1016 | h1016
                                              · linarith only [h1, h1016, hlam]
                                              · rcases p994_3 (m.d 1 4) (by simp) with h1018 | h1018
                                                · linarith only [h1018, h2, hlam]
                                                · linarith only [h1018, h989, hlam]
                                          · linarith only [h1013, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h0, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h9, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h554, hlam, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h664, hlam, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h1, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h940, h990, h993, hc12, hc23, hlam, hphi, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h715, hlam, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h940, hlam, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h2, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h0, h4, h715, h990, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h0, h4, h715, h9, h940, h990, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h3, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h0, h4, h9, h940, h990, h993, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p994_1]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [h989, hlam, p994_0]
                                        · obtain ⟨p994_0, p994_1, p994_2, p994_3⟩ := h994c
                                          linarith only [hlam, p994_0]
                                      · linarith only [h715, h989, h993, hlam]
                                    · linarith only [h554, h715, h989, h992, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h715, h9, h990, h991, hc12, hc35, hlam, hphi, ht23]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1045 | h1045
                                  · linarith only [h1045, h9, h940, h990, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1047 | h1047
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1048 | h1048
                                      · rcases h1bigk with h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          rcases p1049_3 (m.d 0 1) (by simp) with h1051 | h1051
                                          · rcases p1049_3 (m.d 1 2) (by simp) with h1052 | h1052
                                            · linarith only [h1052, hlam, p1049_0]
                                            · rcases p1049_3 (m.d 1 3) (by simp) with h1054 | h1054
                                              · linarith only [h1, h1054, hlam]
                                              · linarith only [h1054, h9, hlam]
                                          · linarith only [h1051, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          rcases p1049_3 (m.d 0 1) (by simp) with h1058 | h1058
                                          · rcases p1049_3 (m.d 1 2) (by simp) with h1059 | h1059
                                            · linarith only [h0, h1059, hlam]
                                            · rcases p1049_3 (m.d 1 3) (by simp) with h1061 | h1061
                                              · linarith only [h1061, hlam, p1049_0]
                                              · rcases p1049_3 (m.d 1 4) (by simp) with h1063 | h1063
                                                · linarith only [h1063, h2, hlam]
                                                · linarith only [h1063, h715, hlam]
                                          · linarith only [h1058, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h989, hc01, hc45, hlam, hphi, ht0b, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          rcases p1049_3 (m.d 0 1) (by simp) with h1068 | h1068
                                          · rcases p1049_3 (m.d 1 2) (by simp) with h1069 | h1069
                                            · linarith only [h0, h1069, hlam]
                                            · rcases p1049_3 (m.d 1 3) (by simp) with h1071 | h1071
                                              · linarith only [h1, h1071, hlam]
                                              · rcases p1049_3 (m.d 1 4) (by simp) with h1073 | h1073
                                                · linarith only [h1073, h2, hlam]
                                                · linarith only [h1073, h989, hlam]
                                          · linarith only [h1068, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h0, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h9, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h554, hlam, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h664, hlam, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h1, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h715, hlam, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h940, hlam, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h2, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h0, h4, h554, h7, h990, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h0, h4, h554, h7, h990, hc01, hc15, hlam, hphi, ht0b, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h3, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h0, h1047, h4, h664, h7, h9, h990, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1049_1]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [h989, hlam, p1049_0]
                                        · obtain ⟨p1049_0, p1049_1, p1049_2, p1049_3⟩ := h1049c
                                          linarith only [hlam, p1049_0]
                                      · linarith only [h1048, h554, h989, h990, hlam]
                                    · linarith only [h1047, h554, h989, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1099 | h1099
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1100 | h1100
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1101 | h1101
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1102 | h1102
                                      · linarith only [h0, h1099, h1102, h4, h715, h9, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · linarith only [h1101, h1102, h715, h9, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1105 | h1105
                                      · linarith only [h0, h1099, h1105, h4, h715, h9, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c | h1107c
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          rcases p1107_3 (m.d 0 1) (by simp) with h1109 | h1109
                                          · rcases p1107_3 (m.d 1 2) (by simp) with h1110 | h1110
                                            · linarith only [h1110, hlam, p1107_0]
                                            · rcases p1107_3 (m.d 1 3) (by simp) with h1112 | h1112
                                              · linarith only [h1, h1112, hlam]
                                              · linarith only [h1112, h9, hlam]
                                          · linarith only [h1109, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          rcases p1107_3 (m.d 0 1) (by simp) with h1116 | h1116
                                          · rcases p1107_3 (m.d 1 2) (by simp) with h1117 | h1117
                                            · linarith only [h0, h1117, hlam]
                                            · rcases p1107_3 (m.d 1 3) (by simp) with h1119 | h1119
                                              · linarith only [h1119, hlam, p1107_0]
                                              · rcases p1107_3 (m.d 1 4) (by simp) with h1121 | h1121
                                                · linarith only [h1121, h2, hlam]
                                                · linarith only [h1121, h715, hlam]
                                          · linarith only [h1116, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          rcases p1107_3 (m.d 0 1) (by simp) with h1125 | h1125
                                          · rcases p1107_3 (m.d 1 2) (by simp) with h1126 | h1126
                                            · linarith only [h0, h1126, hlam]
                                            · rcases p1107_3 (m.d 1 3) (by simp) with h1128 | h1128
                                              · linarith only [h1, h1128, hlam]
                                              · rcases p1107_3 (m.d 1 4) (by simp) with h1130 | h1130
                                                · linarith only [h1130, hlam, p1107_0]
                                                · rcases p1107_3 (m.d 1 5) (by simp) with h1132 | h1132
                                                  · linarith only [h1132, h3, hlam]
                                                  · linarith only [h1132, h989, hlam]
                                          · linarith only [h1125, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          rcases p1107_3 (m.d 0 1) (by simp) with h1136 | h1136
                                          · rcases p1107_3 (m.d 1 2) (by simp) with h1137 | h1137
                                            · linarith only [h0, h1137, hlam]
                                            · rcases p1107_3 (m.d 1 3) (by simp) with h1139 | h1139
                                              · linarith only [h1, h1139, hlam]
                                              · rcases p1107_3 (m.d 1 4) (by simp) with h1141 | h1141
                                                · linarith only [h1141, h2, hlam]
                                                · rcases p1107_3 (m.d 1 5) (by simp) with h1143 | h1143
                                                  · linarith only [h1143, hlam, p1107_0]
                                                  · rcases h2bigk with h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h1099, h1101, h4, h7, h715, h8, h9, hlam, p1145_2]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h0, h1099, h715, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      rcases p1145_3 (m.d 0 2) (by simp) with h1149 | h1149
                                                      · rcases p1145_3 (m.d 1 2) (by simp) with h1150 | h1150
                                                        · linarith only [h0, h1150, hlam]
                                                        · rcases p1145_3 (m.d 2 3) (by simp) with h1152 | h1152
                                                          · linarith only [h1152, h4, hlam]
                                                          · linarith only [h1099, h1152, hlam]
                                                      · linarith only [h1149, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      rcases p1145_3 (m.d 0 2) (by simp) with h1156 | h1156
                                                      · rcases p1145_3 (m.d 1 2) (by simp) with h1157 | h1157
                                                        · linarith only [h0, h1157, hlam]
                                                        · rcases p1145_3 (m.d 2 3) (by simp) with h1159 | h1159
                                                          · linarith only [h1159, h4, hlam]
                                                          · linarith only [h1100, h1159, hlam]
                                                      · linarith only [h1156, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h0, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h9, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h554, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h664, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h4, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      rcases p1145_3 (m.d 0 2) (by simp) with h1169 | h1169
                                                      · rcases p1145_3 (m.d 1 2) (by simp) with h1170 | h1170
                                                        · linarith only [h1170, hlam, p1145_0]
                                                        · rcases p1145_3 (m.d 2 3) (by simp) with h1172 | h1172
                                                          · rcases p1145_3 (m.d 2 4) (by simp) with h1173 | h1173
                                                            · linarith only [h1099, h1173, hlam]
                                                            · linarith only [h1173, h554, hlam]
                                                          · linarith only [h1172, hlam, p1145_0]
                                                      · linarith only [h0, h1169, hlam]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h0, h4, h554, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h0, h1099, h1101, h4, h715, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h5, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h0, h1101, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h1099, hlam, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h1101, hlam, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h6, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      rcases p1145_3 (m.d 0 2) (by simp) with h1187 | h1187
                                                      · rcases p1145_3 (m.d 1 2) (by simp) with h1188 | h1188
                                                        · linarith only [h1188, hlam, p1145_0]
                                                        · rcases p1145_3 (m.d 2 3) (by simp) with h1190 | h1190
                                                          · rcases p1145_3 (m.d 2 4) (by simp) with h1191 | h1191
                                                            · linarith only [h1101, h1191, hlam]
                                                            · linarith only [h1191, h554, hlam]
                                                          · linarith only [h1190, h9, hlam]
                                                      · linarith only [h0, h1187, hlam]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h1100, hlam, p1145_0]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [h0, h554, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1145_1]
                                                    · obtain ⟨p1145_0, p1145_1, p1145_2, p1145_3⟩ := h1145c
                                                      linarith only [hlam, p1145_0]
                                          · linarith only [h1136, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h0, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h9, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h554, hlam, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h664, hlam, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h1, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h715, hc12, hc34, hlam, hphi, ht23, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h715, hlam, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h940, hlam, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h2, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h554, hc12, hc24, hlam, hphi, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h0, h4, h7, h715, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h989, hlam, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h3, hlam, p1107_0]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h0, h6, h664, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [h0, h4, h7, h8, h989, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1107_1]
                                        · obtain ⟨p1107_0, p1107_1, p1107_2, p1107_3⟩ := h1107c
                                          linarith only [hlam, p1107_0]
                                  · linarith only [h1099, h1100, h715, h9, hc12, hc35, hlam, hphi, ht23]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1221 | h1221
                                  · linarith only [h1099, h1221, h9, h940, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1223 | h1223
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1224 | h1224
                                      · rcases h1bigk with h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          rcases p1225_3 (m.d 0 1) (by simp) with h1227 | h1227
                                          · rcases p1225_3 (m.d 1 2) (by simp) with h1228 | h1228
                                            · linarith only [h1228, hlam, p1225_0]
                                            · rcases p1225_3 (m.d 1 3) (by simp) with h1230 | h1230
                                              · linarith only [h1, h1230, hlam]
                                              · linarith only [h1230, h9, hlam]
                                          · linarith only [h1227, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          rcases p1225_3 (m.d 0 1) (by simp) with h1234 | h1234
                                          · rcases p1225_3 (m.d 1 2) (by simp) with h1235 | h1235
                                            · linarith only [h0, h1235, hlam]
                                            · rcases p1225_3 (m.d 1 3) (by simp) with h1237 | h1237
                                              · linarith only [h1237, hlam, p1225_0]
                                              · rcases p1225_3 (m.d 1 4) (by simp) with h1239 | h1239
                                                · linarith only [h1239, h2, hlam]
                                                · linarith only [h1239, h715, hlam]
                                          · linarith only [h1234, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          rcases p1225_3 (m.d 0 1) (by simp) with h1243 | h1243
                                          · rcases p1225_3 (m.d 1 2) (by simp) with h1244 | h1244
                                            · linarith only [h0, h1244, hlam]
                                            · rcases p1225_3 (m.d 1 3) (by simp) with h1246 | h1246
                                              · linarith only [h1, h1246, hlam]
                                              · rcases p1225_3 (m.d 1 4) (by simp) with h1248 | h1248
                                                · linarith only [h1248, hlam, p1225_0]
                                                · rcases p1225_3 (m.d 1 5) (by simp) with h1250 | h1250
                                                  · linarith only [h1250, h3, hlam]
                                                  · linarith only [h1250, h989, hlam]
                                          · linarith only [h1243, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          rcases p1225_3 (m.d 0 1) (by simp) with h1254 | h1254
                                          · rcases p1225_3 (m.d 1 2) (by simp) with h1255 | h1255
                                            · linarith only [h0, h1255, hlam]
                                            · rcases p1225_3 (m.d 1 3) (by simp) with h1257 | h1257
                                              · linarith only [h1, h1257, hlam]
                                              · rcases p1225_3 (m.d 1 4) (by simp) with h1259 | h1259
                                                · linarith only [h1259, h2, hlam]
                                                · rcases p1225_3 (m.d 1 5) (by simp) with h1261 | h1261
                                                  · linarith only [h1261, hlam, p1225_0]
                                                  · rcases h2bigk with h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h1221, h1224, h4, h7, h9, hlam, p1263_2]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      rcases p1263_3 (m.d 0 2) (by simp) with h1266 | h1266
                                                      · rcases p1263_3 (m.d 1 2) (by simp) with h1267 | h1267
                                                        · linarith only [h0, h1267, hlam]
                                                        · rcases p1263_3 (m.d 2 3) (by simp) with h1269 | h1269
                                                          · linarith only [h1269, hlam, p1263_0]
                                                          · rcases p1263_3 (m.d 2 4) (by simp) with h1271 | h1271
                                                            · linarith only [h1271, h5, hlam]
                                                            · linarith only [h1099, h1271, hlam]
                                                      · linarith only [h1266, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h0, h1223, h715, h9, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1263_1]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      rcases p1263_3 (m.d 0 2) (by simp) with h1276 | h1276
                                                      · rcases p1263_3 (m.d 1 2) (by simp) with h1277 | h1277
                                                        · linarith only [h0, h1277, hlam]
                                                        · rcases p1263_3 (m.d 2 3) (by simp) with h1279 | h1279
                                                          · linarith only [h1279, h4, hlam]
                                                          · rcases p1263_3 (m.d 2 4) (by simp) with h1281 | h1281
                                                            · linarith only [h1281, h5, hlam]
                                                            · linarith only [h1223, h1281, hlam]
                                                      · linarith only [h1276, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h0, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h9, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h554, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h664, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h4, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h0, h1221, h1224, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1263_1]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h1099, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h1221, hlam, p1263_1]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h5, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      rcases p1263_3 (m.d 0 2) (by simp) with h1296 | h1296
                                                      · rcases p1263_3 (m.d 1 2) (by simp) with h1297 | h1297
                                                        · linarith only [h1297, hlam, p1263_0]
                                                        · rcases p1263_3 (m.d 2 3) (by simp) with h1299 | h1299
                                                          · linarith only [h1099, h1299, hlam]
                                                          · linarith only [h1299, h9, hlam]
                                                      · linarith only [h0, h1296, hlam]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h9, hc12, hc24, hlam, hphi, p1263_1]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h0, h1099, h4, h664, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1263_1]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h6, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      rcases p1263_3 (m.d 0 2) (by simp) with h1307 | h1307
                                                      · rcases p1263_3 (m.d 1 2) (by simp) with h1308 | h1308
                                                        · linarith only [h1308, hlam, p1263_0]
                                                        · rcases p1263_3 (m.d 2 3) (by simp) with h1310 | h1310
                                                          · linarith only [h1221, h1310, hlam]
                                                          · linarith only [h1310, h9, hlam]
                                                      · linarith only [h0, h1307, hlam]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h9, hc12, hc25, hlam, hphi, p1263_1]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [h1223, hlam, p1263_0]
                                                    · obtain ⟨p1263_0, p1263_1, p1263_2, p1263_3⟩ := h1263c
                                                      linarith only [hlam, p1263_0]
                                          · linarith only [h1254, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h0, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h9, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h554, hlam, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h664, hlam, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h1, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h715, h989, hc12, hc45, hlam, hphi, ht23, ht34, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h715, hlam, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h940, hlam, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h2, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h0, h4, h7, h8, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h0, h4, h7, h8, h989, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h989, hlam, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h3, hlam, p1225_0]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h0, h1224, h4, h7, h9, h940, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [h0, h1224, h4, h7, h940, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1225_1]
                                        · obtain ⟨p1225_0, p1225_1, p1225_2, p1225_3⟩ := h1225c
                                          linarith only [hlam, p1225_0]
                                      · linarith only [h1099, h1223, h1224, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1339 | h1339
                                      · linarith only [h0, h1099, h1223, h1339, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · linarith only [h1099, h1339, h9, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                · linarith only [h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc25, hlam, hphi, ht01, ht12, u0ehi1]
            · linarith only [h4, h5, hc24, hlam, hphi, ht01, ht12, u0ehi2]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA2_H_R_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2bigk := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                    · linarith only [h0, h14, h17, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h14, h16, h17, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                                    · linarith only [h0, h11, h16, h20, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h1bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h15, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h11, h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        rcases p22_3 (m.d 0 1) (by simp) with h27 | h27
                                        · rcases p22_3 (m.d 1 2) (by simp) with h28 | h28
                                          · linarith only [h0, h28, hlam]
                                          · linarith only [h10, h28, hlam]
                                        · linarith only [h27, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h0, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h11, h13, h14, h16, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h0, h13, h14, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p22_1, u1ehi4]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h1, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h8, hlam, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h13, h14, h16, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22_1]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p22_1, u1ehi4]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h2, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h9, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h11, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [hc14, hlam, hphi, p22_1, u1ehi4]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h3, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h10, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h12, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [h13, hlam, p22_0]
                                      · obtain ⟨p22_0, p22_1, p22_2, p22_3⟩ := h22c
                                        linarith only [hlam, p22_0]
                                · linarith only [h0, h12, h14, h15, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                                · linarith only [h0, h11, h14, h53, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                                    · rcases h1bigk with h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h11, h53, h56, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p57_1]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h11, h53, h56, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p57_1]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        rcases p57_3 (m.d 0 1) (by simp) with h61 | h61
                                        · rcases p57_3 (m.d 1 2) (by simp) with h62 | h62
                                          · linarith only [h0, h62, hlam]
                                          · linarith only [h62, h9, hlam]
                                        · linarith only [h61, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        rcases p57_3 (m.d 0 1) (by simp) with h66 | h66
                                        · rcases p57_3 (m.d 1 2) (by simp) with h67 | h67
                                          · linarith only [h0, h67, hlam]
                                          · linarith only [h10, h67, hlam]
                                        · linarith only [h66, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h0, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h11, h53, h56, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p57_1]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p57_1, u1ehi3]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p57_1, u1ehi4]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h1, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h8, hlam, p57_1]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hc13, hlam, hphi, p57_1, u1ehi3]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p57_1, u1ehi4]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h2, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h9, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h11, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hc14, hlam, hphi, p57_1, u1ehi4]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h3, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h10, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h12, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [h13, hlam, p57_0]
                                      · obtain ⟨p57_0, p57_1, p57_2, p57_3⟩ := h57c
                                        linarith only [hlam, p57_0]
                                    · linarith only [h0, h11, h13, h14, h56, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                                    · linarith only [h0, h11, h55, h8, h92, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h0, h11, h13, h14, h8, h92, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                                  · linarith only [h13, h97, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                                    · linarith only [h13, h95, h99, hc23, hlam, hphi, ht12, u1ehi3]
                                    · rcases h1bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h8, h96, h99, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p101_1]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        rcases p101_3 (m.d 0 1) (by simp) with h104 | h104
                                        · rcases p101_3 (m.d 1 2) (by simp) with h105 | h105
                                          · linarith only [h0, h105, hlam]
                                          · linarith only [h105, h8, hlam]
                                        · linarith only [h104, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        rcases p101_3 (m.d 0 1) (by simp) with h109 | h109
                                        · rcases p101_3 (m.d 1 2) (by simp) with h110 | h110
                                          · linarith only [h0, h110, hlam]
                                          · linarith only [h110, h9, hlam]
                                        · linarith only [h109, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        rcases p101_3 (m.d 0 1) (by simp) with h114 | h114
                                        · rcases p101_3 (m.d 1 2) (by simp) with h115 | h115
                                          · linarith only [h0, h115, hlam]
                                          · linarith only [h10, h115, hlam]
                                        · linarith only [h114, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h0, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hc12, hlam, hphi, p101_1, u1ehi2]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p101_1, u1ehi3]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h0, h13, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p101_1, u1ehi3]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h1, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h8, hlam, p101_1]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hc13, hlam, hphi, p101_1, u1ehi3]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p101_1, u1ehi3]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h2, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h9, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h11, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h13, hlam, p101_1]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h3, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h10, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [h12, hlam, p101_0]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hc15, hlam, hphi, p101_1, u1ehi3]
                                      · obtain ⟨p101_0, p101_1, p101_2, p101_3⟩ := h101c
                                        linarith only [hlam, p101_0]
                                · linarith only [h0, h12, h8, h95, h96, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                                · linarith only [h0, h11, h140, h8, h95, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                                  · linarith only [h13, h142, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                                    · linarith only [h11, h13, h144, hlam]
                                    · rcases h1bigk with h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h11, h8, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p146_1]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h11, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p146_1]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        rcases p146_3 (m.d 0 1) (by simp) with h150 | h150
                                        · rcases p146_3 (m.d 1 2) (by simp) with h151 | h151
                                          · linarith only [h0, h151, hlam]
                                          · linarith only [h151, h9, hlam]
                                        · linarith only [h150, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        rcases p146_3 (m.d 0 1) (by simp) with h155 | h155
                                        · rcases p146_3 (m.d 1 2) (by simp) with h156 | h156
                                          · linarith only [h0, h156, hlam]
                                          · linarith only [h10, h156, hlam]
                                        · linarith only [h155, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h0, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h12, h144, h95, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p146_1]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p146_1, u1ehi3]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p146_1, u1ehi4]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h1, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h8, hlam, p146_1]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hc13, hlam, hphi, p146_1, u1ehi3]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p146_1, u1ehi4]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h2, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h9, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h11, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h13, hlam, p146_1]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h3, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h10, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [h12, hlam, p146_0]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hc15, hlam, hphi, p146_1, u1ehi3]
                                      · obtain ⟨p146_0, p146_1, p146_2, p146_3⟩ := h146c
                                        linarith only [hlam, p146_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                            · linarith only [h11, h12, h180, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                                · linarith only [h12, h183, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                                  · linarith only [h180, h185, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                    · linarith only [h180, h182, h187, h8, hc13, hlam, hphi, u1ehi3]
                                    · rcases h1bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h182, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p189_1]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        rcases p189_3 (m.d 0 1) (by simp) with h192 | h192
                                        · rcases p189_3 (m.d 1 2) (by simp) with h193 | h193
                                          · linarith only [h0, h193, hlam]
                                          · linarith only [h193, h8, hlam]
                                        · linarith only [h192, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        rcases p189_3 (m.d 0 1) (by simp) with h197 | h197
                                        · rcases p189_3 (m.d 1 2) (by simp) with h198 | h198
                                          · linarith only [h0, h198, hlam]
                                          · linarith only [h198, h9, hlam]
                                        · linarith only [h197, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        rcases p189_3 (m.d 0 1) (by simp) with h202 | h202
                                        · rcases p189_3 (m.d 1 2) (by simp) with h203 | h203
                                          · linarith only [h0, h203, hlam]
                                          · linarith only [h10, h203, hlam]
                                        · linarith only [h202, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h0, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hc12, hlam, hphi, p189_1, u1ehi2]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p189_1, u1ehi3]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p189_1, u1ehi4]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h1, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h8, hlam, p189_1]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hc13, hlam, hphi, p189_1, u1ehi3]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h12, hlam, p189_1]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h2, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h9, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h11, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h180, hlam, p189_1]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h3, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h10, hlam, p189_0]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hc15, hlam, hphi, p189_1, u1ehi2]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [h0, h12, h187, h4, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p189_1, u1ehi3]
                                      · obtain ⟨p189_0, p189_1, p189_2, p189_3⟩ := h189c
                                        linarith only [hlam, p189_0]
                              · linarith only [h11, h12, h182, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                              · linarith only [h11, h230, h8, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                                    · rcases h1bigk with h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h232, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p235_1]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        rcases p235_3 (m.d 0 1) (by simp) with h238 | h238
                                        · rcases p235_3 (m.d 1 2) (by simp) with h239 | h239
                                          · linarith only [h0, h239, hlam]
                                          · linarith only [h239, h8, hlam]
                                        · linarith only [h238, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        rcases p235_3 (m.d 0 1) (by simp) with h243 | h243
                                        · rcases p235_3 (m.d 1 2) (by simp) with h244 | h244
                                          · linarith only [h0, h244, hlam]
                                          · linarith only [h244, h9, hlam]
                                        · linarith only [h243, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        rcases p235_3 (m.d 0 1) (by simp) with h248 | h248
                                        · rcases p235_3 (m.d 1 2) (by simp) with h249 | h249
                                          · linarith only [h0, h249, hlam]
                                          · linarith only [h10, h249, hlam]
                                        · linarith only [h248, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h0, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h228, hc12, hlam, hphi, p235_1, u1ehi4]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h0, h11, h228, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi4]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi4]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h1, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h8, hlam, p235_1]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h11, hlam, p235_1]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hc13, hlam, hphi, p235_1, u1ehi4]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h2, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h9, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hc14, hlam, hphi, p235_1, u1ehi2]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h0, h11, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi4]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h3, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h10, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h228, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [h229, hlam, p235_0]
                                      · obtain ⟨p235_0, p235_1, p235_2, p235_3⟩ := h235c
                                        linarith only [hlam, p235_0]
                                    · linarith only [h11, h234, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                  · linarith only [h2, h229, h230, h232, h233, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h11, h228, h232, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h11, h228, h229, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                              · linarith only [h11, h278, h8, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                                · linarith only [h228, h280, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                                    · rcases h1bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h282, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p284_1]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        rcases p284_3 (m.d 0 1) (by simp) with h287 | h287
                                        · rcases p284_3 (m.d 1 2) (by simp) with h288 | h288
                                          · linarith only [h0, h288, hlam]
                                          · linarith only [h288, h8, hlam]
                                        · linarith only [h287, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        rcases p284_3 (m.d 0 1) (by simp) with h292 | h292
                                        · rcases p284_3 (m.d 1 2) (by simp) with h293 | h293
                                          · linarith only [h0, h293, hlam]
                                          · linarith only [h293, h9, hlam]
                                        · linarith only [h292, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        rcases p284_3 (m.d 0 1) (by simp) with h297 | h297
                                        · rcases p284_3 (m.d 1 2) (by simp) with h298 | h298
                                          · linarith only [h0, h298, hlam]
                                          · linarith only [h10, h298, hlam]
                                        · linarith only [h297, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h0, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hc12, hlam, hphi, p284_1, u1ehi2]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h0, h228, h277, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi2]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h0, h228, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi2]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h1, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h8, hlam, p284_1]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h11, hlam, p284_1]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h228, hlam, p284_1]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h2, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h9, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hc14, hlam, hphi, p284_1, u1ehi2]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h0, h11, h228, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p284_1, u1ehi2]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h3, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h10, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hc15, hlam, hphi, p284_1, u1ehi2]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [h277, hlam, p284_0]
                                      · obtain ⟨p284_0, p284_1, p284_2, p284_3⟩ := h284c
                                        linarith only [hlam, p284_0]
                                    · linarith only [h11, h282, h283, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
                                    · rcases h1bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h277, h278, h282, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        rcases p324_3 (m.d 0 1) (by simp) with h327 | h327
                                        · rcases p324_3 (m.d 1 2) (by simp) with h328 | h328
                                          · linarith only [h0, h328, hlam]
                                          · linarith only [h328, h8, hlam]
                                        · linarith only [h327, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h277, h278, h282, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        rcases p324_3 (m.d 0 1) (by simp) with h333 | h333
                                        · rcases p324_3 (m.d 1 2) (by simp) with h334 | h334
                                          · linarith only [h0, h334, hlam]
                                          · linarith only [h10, h334, hlam]
                                        · linarith only [h333, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h0, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hc12, hlam, hphi, p324_1, u1ehi2]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h0, h277, h278, h282, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h0, h228, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p324_1, u1ehi2]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h1, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h8, hlam, p324_1]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h11, hlam, p324_1]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h228, hlam, p324_1]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h2, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h9, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hc14, hlam, hphi, p324_1, u1ehi2]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h0, h11, h228, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p324_1, u1ehi2]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h3, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h10, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hc15, hlam, hphi, p324_1, u1ehi2]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [h277, hlam, p324_0]
                                      · obtain ⟨p324_0, p324_1, p324_2, p324_3⟩ := h324c
                                        linarith only [hlam, p324_0]
                                    · linarith only [h0, h11, h323, h4, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                              · linarith only [h11, h359, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h361 | h361
                                · linarith only [h228, h361, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h363 | h363
                                  · linarith only [h277, h363, h9, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h365 | h365
                                    · linarith only [h277, h365, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                    · linarith only [h11, h365, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h369 | h369
                          · linarith only [h10, h369, h8, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h371 | h371
                            · linarith only [h10, h371, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                              · linarith only [h0, h10, h373, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h10, h368, h373, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
                          · linarith only [h10, h368, h376, h9, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
                            · linarith only [h10, h378, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                              · linarith only [h368, h380, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                                · linarith only [h0, h10, h376, h380, h382, h5, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                                  · linarith only [h0, h10, h378, h384, h5, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                                    · linarith only [h10, h380, h384, h386, h9, hc23, hc34, hlam, hphi]
                                    · linarith only [h0, h368, h386, h4, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                        · linarith only [h390, h8, h9, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h392 | h392
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                              · linarith only [h390, h394, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                                · linarith only [h0, h394, h396, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h392, h394, h396, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h389, h393, h9, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h400 | h400
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                              · linarith only [h390, h401, h8, hc12, hlam, hphi, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h403 | h403
                                · linarith only [h0, h392, h4, h401, h403, h6, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h406 | h406
                                    · rcases h1bigk with h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        rcases p407_3 (m.d 0 1) (by simp) with h409 | h409
                                        · rcases p407_3 (m.d 1 2) (by simp) with h410 | h410
                                          · linarith only [h410, hlam, p407_0]
                                          · rcases p407_3 (m.d 1 3) (by simp) with h412 | h412
                                            · linarith only [h1, h412, hlam]
                                            · rcases p407_3 (m.d 1 4) (by simp) with h414 | h414
                                              · linarith only [h2, h414, hlam]
                                              · linarith only [h414, h9, hlam]
                                        · linarith only [h409, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        rcases p407_3 (m.d 0 1) (by simp) with h418 | h418
                                        · rcases p407_3 (m.d 1 2) (by simp) with h419 | h419
                                          · linarith only [h0, h419, hlam]
                                          · linarith only [h419, h8, hlam]
                                        · linarith only [h418, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        rcases p407_3 (m.d 0 1) (by simp) with h423 | h423
                                        · rcases p407_3 (m.d 1 2) (by simp) with h424 | h424
                                          · linarith only [h0, h424, hlam]
                                          · rcases p407_3 (m.d 1 3) (by simp) with h426 | h426
                                            · linarith only [h1, h426, hlam]
                                            · rcases p407_3 (m.d 1 4) (by simp) with h428 | h428
                                              · linarith only [h428, hlam, p407_0]
                                              · rcases p407_3 (m.d 1 5) (by simp) with h430 | h430
                                                · linarith only [h3, h430, hlam]
                                                · rcases h2bigk with h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    rcases p432_3 (m.d 0 2) (by simp) with h434 | h434
                                                    · rcases p432_3 (m.d 1 2) (by simp) with h435 | h435
                                                      · linarith only [h0, h435, hlam]
                                                      · rcases p432_3 (m.d 2 3) (by simp) with h437 | h437
                                                        · linarith only [h4, h437, hlam]
                                                        · rcases p432_3 (m.d 2 4) (by simp) with h439 | h439
                                                          · linarith only [h4, h401, h439, h6, hlam]
                                                          · linarith only [h439, h9, hlam]
                                                    · linarith only [h0, h434, hlam]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h389, h4, h401, h403, h6, h9, hlam, p432_2]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h0, h389, h403, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p432_1]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h389, h4, h401, h6, h9, hlam, p432_2]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h0, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1, p432_1]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h9, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p407_1, p432_1]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h4, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h8, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h401, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h403, hlam, p432_1]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h4, h401, h6, hlam, p432_1]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h389, h392, h4, h401, h6, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p432_1, u1ehi2]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    rcases p432_3 (m.d 0 2) (by simp) with h458 | h458
                                                    · rcases p432_3 (m.d 1 2) (by simp) with h459 | h459
                                                      · linarith only [h459, h9, hlam]
                                                      · linarith only [h459, h8, hlam]
                                                    · linarith only [h4, h458, hlam]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    rcases p432_3 (m.d 0 2) (by simp) with h464 | h464
                                                    · rcases p432_3 (m.d 1 2) (by simp) with h465 | h465
                                                      · linarith only [h465, h9, hlam]
                                                      · linarith only [h389, h465, hlam]
                                                    · linarith only [h464, h5, hlam]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h5, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h389, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h0, h389, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p432_1]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [h405, hlam, p432_0]
                                                  · obtain ⟨p432_0, p432_1, p432_2, p432_3⟩ := h432c
                                                    linarith only [hlam, p432_0]
                                        · linarith only [h423, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        rcases p407_3 (m.d 0 1) (by simp) with h475 | h475
                                        · rcases p407_3 (m.d 1 2) (by simp) with h476 | h476
                                          · linarith only [h0, h476, hlam]
                                          · linarith only [h389, h476, hlam]
                                        · linarith only [h475, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h0, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h0, h4, h401, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p407_1, u1ehi2]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h9, hlam, p407_1]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h0, h392, h4, h401, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p407_1, u1ehi2]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h1, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h8, hlam, p407_1]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h390, hlam, p407_1]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h392, hlam, p407_1]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h2, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hc14, hlam, hphi, p407_1, u1ehi1]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h0, h4, h401, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p407_1, u1ehi2]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h0, h4, h401, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p407_1, u1ehi4]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h3, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h389, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hc15, hlam, hphi, p407_1, u1ehi2]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [h400, hlam, p407_0]
                                      · obtain ⟨p407_0, p407_1, p407_2, p407_3⟩ := h407c
                                        linarith only [hlam, p407_0]
                                    · linarith only [h401, h406, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                  · linarith only [h389, h400, h405, h9, hlam]
                            · linarith only [h389, h400, h9, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h503 | h503
                        · linarith only [h503, h8, h9, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
                          · linarith only [h389, h505, h8, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h507 | h507
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                              · linarith only [h503, h508, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h510 | h510
                                · linarith only [h505, h510, h8, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h513 | h513
                                    · rcases h1bigk with h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        rcases p514_3 (m.d 0 1) (by simp) with h516 | h516
                                        · rcases p514_3 (m.d 1 2) (by simp) with h517 | h517
                                          · linarith only [h517, hlam, p514_0]
                                          · rcases p514_3 (m.d 1 3) (by simp) with h519 | h519
                                            · linarith only [h1, h519, hlam]
                                            · rcases p514_3 (m.d 1 4) (by simp) with h521 | h521
                                              · linarith only [h2, h521, hlam]
                                              · linarith only [h521, h9, hlam]
                                        · linarith only [h516, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        rcases p514_3 (m.d 0 1) (by simp) with h525 | h525
                                        · rcases p514_3 (m.d 1 2) (by simp) with h526 | h526
                                          · linarith only [h0, h526, hlam]
                                          · linarith only [h526, h8, hlam]
                                        · linarith only [h525, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        rcases p514_3 (m.d 0 1) (by simp) with h530 | h530
                                        · rcases p514_3 (m.d 1 2) (by simp) with h531 | h531
                                          · linarith only [h0, h531, hlam]
                                          · rcases p514_3 (m.d 1 3) (by simp) with h533 | h533
                                            · linarith only [h1, h533, hlam]
                                            · rcases p514_3 (m.d 1 4) (by simp) with h535 | h535
                                              · linarith only [h535, hlam, p514_0]
                                              · rcases p514_3 (m.d 1 5) (by simp) with h537 | h537
                                                · linarith only [h3, h537, hlam]
                                                · rcases h2bigk with h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    rcases p539_3 (m.d 0 2) (by simp) with h541 | h541
                                                    · rcases p539_3 (m.d 1 2) (by simp) with h542 | h542
                                                      · linarith only [h0, h542, hlam]
                                                      · rcases p539_3 (m.d 2 3) (by simp) with h544 | h544
                                                        · linarith only [h4, h544, hlam]
                                                        · rcases p539_3 (m.d 2 4) (by simp) with h546 | h546
                                                          · linarith only [h4, h508, h546, h6, hlam]
                                                          · linarith only [h546, h9, hlam]
                                                    · linarith only [h0, h541, hlam]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h389, h4, h508, h512, h6, h8, hlam, p539_2]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h0, h389, h512, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h0, h389, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi1]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h0, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h389, h510, hc23, hc35, hlam, hphi, p539_1]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h9, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h389, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h4, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h8, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h508, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h510, hlam, p539_1]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h4, h508, h6, hlam, p539_1]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h0, h4, h508, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi1]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    rcases p539_3 (m.d 0 2) (by simp) with h565 | h565
                                                    · rcases p539_3 (m.d 1 2) (by simp) with h566 | h566
                                                      · linarith only [h566, h9, hlam]
                                                      · linarith only [h566, h8, hlam]
                                                    · linarith only [h4, h565, hlam]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h0, h389, h4, h508, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p539_1, u1ehi2]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h5, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h8, hc25, hlam, hphi, ht12, p539_1, u1ehi2]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    rcases p539_3 (m.d 0 2) (by simp) with h574 | h574
                                                    · rcases p539_3 (m.d 1 2) (by simp) with h575 | h575
                                                      · linarith only [h389, h575, hlam]
                                                      · linarith only [h575, h8, hlam]
                                                    · linarith only [h4, h574, hlam]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [h512, hlam, p539_0]
                                                  · obtain ⟨p539_0, p539_1, p539_2, p539_3⟩ := h539c
                                                    linarith only [hlam, p539_0]
                                        · linarith only [h530, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        rcases p514_3 (m.d 0 1) (by simp) with h582 | h582
                                        · rcases p514_3 (m.d 1 2) (by simp) with h583 | h583
                                          · linarith only [h0, h583, hlam]
                                          · rcases p514_3 (m.d 1 3) (by simp) with h585 | h585
                                            · linarith only [h1, h585, hlam]
                                            · rcases p514_3 (m.d 1 4) (by simp) with h587 | h587
                                              · linarith only [h2, h587, hlam]
                                              · linarith only [h507, h587, hlam]
                                        · linarith only [h582, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h0, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hc12, hlam, hphi, p514_1, u1ehi2]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h9, hlam, p514_1]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h389, hlam, p514_1]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h1, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h8, hlam, p514_1]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h503, hlam, p514_1]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h505, hlam, p514_1]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h2, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hc14, hlam, hphi, p514_1, u1ehi1]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h0, h4, h508, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p514_1, u1ehi2]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h0, h4, h508, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p514_1, u1ehi4]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h3, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h8, hc15, hlam, hphi, p514_1, u1ehi2]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h0, h389, h4, h510, h513, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p514_1, u1ehi2]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [h507, hlam, p514_0]
                                      · obtain ⟨p514_0, p514_1, p514_2, p514_3⟩ := h514c
                                        linarith only [hlam, p514_0]
                                    · linarith only [h507, h508, h513, h9, hlam]
                                  · linarith only [h507, h512, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                              · linarith only [h0, h4, h507, h6, h613, h7, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                                · linarith only [h0, h4, h507, h6, h615, h7, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                                  · linarith only [h507, h613, h617, h8, h9, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h4, h6, h617, h7, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h620 | h620
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h621 | h621
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                                  · linarith only [h0, h4, h620, h627, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h4, h620, h624, h627, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h620, h624, h626, h8, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                              · linarith only [h620, h624, h625, h8, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h632 | h632
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h634 | h634
                                  · linarith only [h0, h4, h620, h634, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h636 | h636
                                    · linarith only [h0, h4, h621, h624, h632, h634, h636, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                    · rcases h1bigk with h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        rcases p638_3 (m.d 0 1) (by simp) with h640 | h640
                                        · rcases p638_3 (m.d 1 2) (by simp) with h641 | h641
                                          · linarith only [h641, hlam, p638_0]
                                          · rcases p638_3 (m.d 1 3) (by simp) with h643 | h643
                                            · linarith only [h1, h643, hlam]
                                            · linarith only [h643, h8, hlam]
                                        · linarith only [h640, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        rcases p638_3 (m.d 0 1) (by simp) with h647 | h647
                                        · rcases p638_3 (m.d 1 2) (by simp) with h648 | h648
                                          · linarith only [h0, h648, hlam]
                                          · rcases p638_3 (m.d 1 3) (by simp) with h650 | h650
                                            · linarith only [h650, hlam, p638_0]
                                            · rcases p638_3 (m.d 1 4) (by simp) with h652 | h652
                                              · linarith only [h2, h652, hlam]
                                              · rcases p638_3 (m.d 1 5) (by simp) with h654 | h654
                                                · linarith only [h3, h654, hlam]
                                                · rcases h2bigk with h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c | h656c
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    rcases p656_3 (m.d 0 2) (by simp) with h658 | h658
                                                    · rcases p656_3 (m.d 1 2) (by simp) with h659 | h659
                                                      · linarith only [h0, h659, hlam]
                                                      · rcases p656_3 (m.d 2 3) (by simp) with h661 | h661
                                                        · linarith only [h4, h661, hlam]
                                                        · linarith only [h661, h8, hlam]
                                                    · linarith only [h0, h658, hlam]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h0, h621, h634, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h4, h620, h8, hlam, p656_2]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h4, h621, h8, hlam, p656_2]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h0, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h8, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p638_1, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p638_1, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h4, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h4, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p656_1, u1ehi1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    rcases p656_3 (m.d 0 2) (by simp) with h676 | h676
                                                    · rcases p656_3 (m.d 1 2) (by simp) with h677 | h677
                                                      · linarith only [h677, h8, hlam]
                                                      · linarith only [h620, h677, hlam]
                                                    · linarith only [h5, h634, h676, hlam]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    rcases p656_3 (m.d 0 2) (by simp) with h681 | h681
                                                    · rcases p656_3 (m.d 1 2) (by simp) with h682 | h682
                                                      · linarith only [h682, h8, hlam]
                                                      · linarith only [h621, h682, hlam]
                                                    · linarith only [h5, h681, hlam]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h4, h621, h634, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h620, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h632, hlam, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h634, hlam, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h5, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h621, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h633, hlam, p656_0]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [h0, h621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p656_1]
                                                  · obtain ⟨p656_0, p656_1, p656_2, p656_3⟩ := h656c
                                                    linarith only [hlam, p656_0]
                                        · linarith only [h647, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        rcases p638_3 (m.d 0 1) (by simp) with h697 | h697
                                        · rcases p638_3 (m.d 1 2) (by simp) with h698 | h698
                                          · linarith only [h0, h698, hlam]
                                          · linarith only [h620, h698, hlam]
                                        · linarith only [h697, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        rcases p638_3 (m.d 0 1) (by simp) with h702 | h702
                                        · rcases p638_3 (m.d 1 2) (by simp) with h703 | h703
                                          · linarith only [h0, h703, hlam]
                                          · linarith only [h621, h703, hlam]
                                        · linarith only [h702, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h0, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h8, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p638_1, u1ehi3]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h0, h4, h624, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p638_1, u1ehi3]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h1, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hc13, hlam, hphi, p638_1, u1ehi1]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p638_1, u1ehi3]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p638_1, u1ehi4]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h2, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h620, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h622, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h624, hlam, p638_1]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h3, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h621, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [h623, hlam, p638_0]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hc15, hlam, hphi, p638_1, u1ehi3]
                                      · obtain ⟨p638_0, p638_1, p638_2, p638_3⟩ := h638c
                                        linarith only [hlam, p638_0]
                                · linarith only [h633, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h621, h624, h632, h8, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h621, h623, h8, hlam]
                        · linarith only [h620, h622, h8, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                            · linarith only [h620, h621, h733, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h735 | h735
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h736 | h736
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h737 | h737
                                  · linarith only [h620, h733, h737, hc12, hlam, hphi, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h739 | h739
                                    · linarith only [h620, h621, h735, h737, h739, hlam]
                                    · rcases h1bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        rcases p741_3 (m.d 0 1) (by simp) with h743 | h743
                                        · rcases p741_3 (m.d 1 2) (by simp) with h744 | h744
                                          · linarith only [h744, hlam, p741_0]
                                          · rcases p741_3 (m.d 1 3) (by simp) with h746 | h746
                                            · linarith only [h1, h746, hlam]
                                            · linarith only [h746, h8, hlam]
                                        · linarith only [h743, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        rcases p741_3 (m.d 0 1) (by simp) with h750 | h750
                                        · rcases p741_3 (m.d 1 2) (by simp) with h751 | h751
                                          · linarith only [h0, h751, hlam]
                                          · rcases p741_3 (m.d 1 3) (by simp) with h753 | h753
                                            · linarith only [h753, hlam, p741_0]
                                            · rcases p741_3 (m.d 1 4) (by simp) with h755 | h755
                                              · linarith only [h2, h755, hlam]
                                              · rcases p741_3 (m.d 1 5) (by simp) with h757 | h757
                                                · linarith only [h3, h757, hlam]
                                                · rcases h2bigk with h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    rcases p759_3 (m.d 0 2) (by simp) with h761 | h761
                                                    · rcases p759_3 (m.d 1 2) (by simp) with h762 | h762
                                                      · linarith only [h0, h762, hlam]
                                                      · rcases p759_3 (m.d 2 3) (by simp) with h764 | h764
                                                        · linarith only [h4, h764, hlam]
                                                        · linarith only [h764, h8, hlam]
                                                    · linarith only [h0, h761, hlam]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h0, h620, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p759_1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h4, h620, h621, h736, hlam, p759_2]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h0, h620, h621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p759_1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h0, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h8, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h0, h5, h621, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p759_1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h621, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h4, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p759_1, u1ehi1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    rcases p759_3 (m.d 0 2) (by simp) with h779 | h779
                                                    · rcases p759_3 (m.d 1 2) (by simp) with h780 | h780
                                                      · linarith only [h780, h8, hlam]
                                                      · linarith only [h620, h780, hlam]
                                                    · linarith only [h4, h620, h779, h8, hc24, hlam, hphi, ht12, u1ehi3]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h4, h620, h621, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p759_1, u1ehi3]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h4, h620, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p759_1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h620, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h735, hlam, p759_1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h737, hlam, p759_1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h5, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [hc25, hlam, hphi, ht12, p759_1, u1ehi1]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [h736, hlam, p759_0]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    rcases p759_3 (m.d 0 2) (by simp) with h793 | h793
                                                    · rcases p759_3 (m.d 1 2) (by simp) with h794 | h794
                                                      · linarith only [h621, h794, hlam]
                                                      · linarith only [h620, h794, hlam]
                                                    · linarith only [h4, h6, h620, h621, h7, h737, h793, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                                  · obtain ⟨p759_0, p759_1, p759_2, p759_3⟩ := h759c
                                                    linarith only [hlam, p759_0]
                                        · linarith only [h750, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        rcases p741_3 (m.d 0 1) (by simp) with h800 | h800
                                        · rcases p741_3 (m.d 1 2) (by simp) with h801 | h801
                                          · linarith only [h0, h801, hlam]
                                          · linarith only [h620, h801, hlam]
                                        · linarith only [h800, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        rcases p741_3 (m.d 0 1) (by simp) with h805 | h805
                                        · rcases p741_3 (m.d 1 2) (by simp) with h806 | h806
                                          · linarith only [h0, h806, hlam]
                                          · rcases p741_3 (m.d 1 3) (by simp) with h808 | h808
                                            · linarith only [h1, h808, hlam]
                                            · linarith only [h732, h808, hlam]
                                        · linarith only [h805, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h0, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h8, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h0, h4, h6, h621, h7, h737, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p741_1, u1ehi3]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h621, hlam, p741_1]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h1, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [hc13, hlam, hphi, p741_1, u1ehi1]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p741_1, u1ehi3]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p741_1, u1ehi4]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h2, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h620, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h731, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h733, hlam, p741_1]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h3, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h620, hc15, hlam, hphi, p741_1, u1ehi3]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h732, hlam, p741_0]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [h0, h4, h6, h621, h7, h737, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p741_1, u1ehi3]
                                      · obtain ⟨p741_0, p741_1, p741_2, p741_3⟩ := h741c
                                        linarith only [hlam, p741_0]
                                · linarith only [h620, h736, h8, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h620, h735, h8, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
                            · linarith only [h620, h621, h834, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h837 | h837
                                · linarith only [h732, h837, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h620, h8, h837, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                              · linarith only [h620, h8, h836, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h620, h731, h8, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h842 | h842
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h843 | h843
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h844 | h844
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h845 | h845
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h846 | h846
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h847 | h847
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h849 | h849
                                    · rcases h1bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        rcases p850_3 (m.d 0 1) (by simp) with h852 | h852
                                        · rcases p850_3 (m.d 1 2) (by simp) with h853 | h853
                                          · linarith only [h853, hlam, p850_0]
                                          · rcases p850_3 (m.d 1 3) (by simp) with h855 | h855
                                            · linarith only [h1, h855, hlam]
                                            · linarith only [h8, h855, hlam]
                                        · linarith only [h852, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h843, h849, hc01, hc45, hlam, hphi, ht0b, ht5b, p850_1]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        rcases p850_3 (m.d 0 1) (by simp) with h860 | h860
                                        · rcases p850_3 (m.d 1 2) (by simp) with h861 | h861
                                          · linarith only [h0, h861, hlam]
                                          · rcases p850_3 (m.d 1 3) (by simp) with h863 | h863
                                            · linarith only [h1, h863, hlam]
                                            · linarith only [h843, h863, hlam]
                                        · linarith only [h860, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        rcases p850_3 (m.d 0 1) (by simp) with h867 | h867
                                        · rcases p850_3 (m.d 1 2) (by simp) with h868 | h868
                                          · linarith only [h0, h868, hlam]
                                          · linarith only [h842, h868, hlam]
                                        · linarith only [h867, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h0, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h8, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h620, hlam, p850_1]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h0, h4, h620, h846, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p850_1, u1ehi4]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h1, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [hc13, hlam, hphi, p850_1, u1ehi1]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h0, h4, h620, h8, h842, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p850_1, u1ehi4]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p850_1, u1ehi4]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h2, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h842, hc14, hlam, hphi, p850_1, u1ehi4]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h843, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h0, h4, h620, h846, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p850_1, u1ehi4]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h3, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h842, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h844, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [h845, hlam, p850_0]
                                      · obtain ⟨p850_0, p850_1, p850_2, p850_3⟩ := h850c
                                        linarith only [hlam, p850_0]
                                    · linarith only [h0, h4, h8, h842, h848, h849, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h620, h848, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h8, h842, h847, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                              · linarith only [h8, h842, h846, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                            · linarith only [h620, h842, h845, hlam]
                          · linarith only [h8, h842, h844, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h898 | h898
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h899 | h899
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h900 | h900
                              · linarith only [h8, h843, h900, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h6, h8, h842, h900, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                            · linarith only [h8, h842, h843, h899, hlam]
                          · linarith only [h8, h842, h898, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h905 | h905
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h906 | h906
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h907 | h907
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h908 | h908
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h909 | h909
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h910 | h910
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h911 | h911
                                    · rcases h1bigk with h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        rcases p912_3 (m.d 0 1) (by simp) with h914 | h914
                                        · rcases p912_3 (m.d 1 2) (by simp) with h915 | h915
                                          · linarith only [h915, hlam, p912_0]
                                          · rcases p912_3 (m.d 1 3) (by simp) with h917 | h917
                                            · linarith only [h1, h917, hlam]
                                            · linarith only [h8, h917, hlam]
                                        · linarith only [h914, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h905, h911, hc01, hc45, hlam, hphi, ht0b, ht5b, p912_1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        rcases p912_3 (m.d 0 1) (by simp) with h922 | h922
                                        · rcases p912_3 (m.d 1 2) (by simp) with h923 | h923
                                          · linarith only [h0, h923, hlam]
                                          · rcases p912_3 (m.d 1 3) (by simp) with h925 | h925
                                            · linarith only [h1, h925, hlam]
                                            · linarith only [h905, h925, hlam]
                                        · linarith only [h922, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        rcases p912_3 (m.d 0 1) (by simp) with h929 | h929
                                        · rcases p912_3 (m.d 1 2) (by simp) with h930 | h930
                                          · linarith only [h0, h930, hlam]
                                          · rcases p912_3 (m.d 1 3) (by simp) with h932 | h932
                                            · linarith only [h1, h932, hlam]
                                            · linarith only [h906, h932, hlam]
                                        · linarith only [h929, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h0, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h8, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h620, hlam, p912_1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h842, hlam, p912_1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h1, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hc13, hlam, hphi, p912_1, u1ehi1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p912_1, u1ehi3]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h0, h4, h8, h842, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p912_1, u1ehi1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h2, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hc14, hlam, hphi, p912_1, u1ehi1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h905, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h0, h4, h620, h842, h908, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p912_1, u1ehi1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h3, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hc15, hlam, hphi, p912_1, u1ehi1]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h906, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [h907, hlam, p912_0]
                                      · obtain ⟨p912_0, p912_1, p912_2, p912_3⟩ := h912c
                                        linarith only [hlam, p912_0]
                                    · rcases h1bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        rcases p956_3 (m.d 0 1) (by simp) with h958 | h958
                                        · rcases p956_3 (m.d 1 2) (by simp) with h959 | h959
                                          · linarith only [h959, hlam, p956_0]
                                          · rcases p956_3 (m.d 1 3) (by simp) with h961 | h961
                                            · linarith only [h1, h961, hlam]
                                            · linarith only [h8, h961, hlam]
                                        · linarith only [h958, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h905, h907, h911, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p956_1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h907, h911, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p956_1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        rcases p956_3 (m.d 0 1) (by simp) with h967 | h967
                                        · rcases p956_3 (m.d 1 2) (by simp) with h968 | h968
                                          · linarith only [h0, h968, hlam]
                                          · rcases p956_3 (m.d 1 3) (by simp) with h970 | h970
                                            · linarith only [h1, h970, hlam]
                                            · linarith only [h906, h970, hlam]
                                        · linarith only [h967, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h0, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h8, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h620, hlam, p956_1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h842, hlam, p956_1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h1, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hc13, hlam, hphi, p956_1, u1ehi1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h0, h4, h8, h907, h911, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p956_1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p956_1, u1ehi4]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h2, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hc14, hlam, hphi, p956_1, u1ehi1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h905, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h0, h4, h620, h842, h908, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p956_1, u1ehi1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h3, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hc15, hlam, hphi, p956_1, u1ehi1]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h906, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [h907, hlam, p956_0]
                                      · obtain ⟨p956_0, p956_1, p956_2, p956_3⟩ := h956c
                                        linarith only [hlam, p956_0]
                                  · linarith only [h0, h4, h6, h620, h7, h910, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                · linarith only [h8, h909, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h4, h6, h8, h908, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h998 | h998
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h999 | h999
                                  · linarith only [h907, h997, h999, hc23, hlam, hphi, ht12, u1ehi3]
                                  · linarith only [h620, h999, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h8, h906, h998, hc13, hlam, hphi, u1ehi1]
                              · linarith only [h0, h4, h6, h7, h8, h905, h906, h907, h997, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1004 | h1004
                            · linarith only [h1004, h905, h906, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1006 | h1006
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1007 | h1007
                                · linarith only [h1007, h906, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h1007, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h1006, h8, h905, hc13, hlam, hphi, u1ehi1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1011 | h1011
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1012 | h1012
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
                              · linarith only [h1013, h905, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h1013, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h1011, h1012, h905, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1017 | h1017
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1018 | h1018
                              · linarith only [h0, h1018, h4, h8, h905, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h1018, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1021 | h1021
                              · linarith only [h1021, h8, h905, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h1021, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc25, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA2_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 1 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
                · linarith only [h5, h9, hlam]
                · linarith only [h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h8, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
              · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, hlam]
                · linarith only [h14, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h13, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h18 | h18
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
                · linarith only [h20, h5, hlam]
                · linarith only [h20, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h19, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 1 3 (by decide) (by decide) with h25 | h25
                · linarith only [h25, h5, hlam]
                · linarith only [h25, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h29 | h29
          · rcases p0_3 (m.d 1 5) (by simp) with h30 | h30
            · rcases m.htr 0 1 2 (by decide) (by decide) with h31 | h31
              · rcases m.htr 0 1 3 (by decide) (by decide) with h32 | h32
                · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h29, h33, hlam]
                  · linarith only [h33, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h32, h5, hlam, p0_1]
              · linarith only [h31, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h38 | h38
              · rcases m.htr 0 1 3 (by decide) (by decide) with h39 | h39
                · rcases m.htr 0 1 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h29, h40, hlam]
                  · linarith only [h40, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h39, h5, hlam, p0_1]
              · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h45 | h45
            · rcases m.htr 0 1 2 (by decide) (by decide) with h46 | h46
              · rcases m.htr 0 1 3 (by decide) (by decide) with h47 | h47
                · rcases m.htr 0 1 4 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h45, h49, hlam]
                    · linarith only [h49, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h29, h48, hlam, p0_1]
                · linarith only [h47, h5, hlam, p0_1]
              · linarith only [h46, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h55 | h55
              · rcases m.htr 0 1 3 (by decide) (by decide) with h56 | h56
                · rcases m.htr 0 1 4 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                      · linarith only [h59, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                      · linarith only [h5, h59, hlam]
                    · linarith only [h45, h58, hlam, p0_1]
                  · linarith only [h29, h57, hlam, p0_1]
                · linarith only [h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h55, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h67 | h67
    · rcases p0_3 (m.d 1 2) (by simp) with h68 | h68
      · rcases p0_3 (m.d 1 3) (by simp) with h69 | h69
        · linarith only [h69, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
          · rcases p0_3 (m.d 1 5) (by simp) with h72 | h72
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · linarith only [h68, h73, hlam]
              · linarith only [h73, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h76 | h76
              · linarith only [h68, h76, hlam]
              · linarith only [h76, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h79 | h79
            · rcases m.htr 0 1 2 (by decide) (by decide) with h80 | h80
              · linarith only [h68, h80, hlam]
              · linarith only [h80, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h83 | h83
              · linarith only [h68, h83, hlam]
              · linarith only [h83, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h86 | h86
        · linarith only [h86, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h88 | h88
          · rcases p0_3 (m.d 1 5) (by simp) with h89 | h89
            · rcases m.htr 0 1 2 (by decide) (by decide) with h90 | h90
              · rcases m.htr 0 1 3 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 1 4 (by decide) (by decide) with h92 | h92
                  · linarith only [h88, h92, hlam]
                  · linarith only [h68, h92, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h91, hlam, p0_0]
              · linarith only [h68, h90, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h97 | h97
              · rcases m.htr 0 1 3 (by decide) (by decide) with h98 | h98
                · rcases m.htr 0 1 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h88, h99, hlam]
                  · linarith only [h68, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h98, hlam, p0_0]
              · linarith only [h68, h97, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h104 | h104
            · rcases m.htr 0 1 2 (by decide) (by decide) with h105 | h105
              · rcases m.htr 0 1 3 (by decide) (by decide) with h106 | h106
                · rcases m.htr 0 1 4 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h104, h108, hlam]
                    · linarith only [h108, h68, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h107, h88, hlam, p0_1]
                · linarith only [h106, hlam, p0_0]
              · linarith only [h105, h68, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h114 | h114
              · rcases m.htr 0 1 3 (by decide) (by decide) with h115 | h115
                · rcases m.htr 0 1 4 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                      · linarith only [h118, h68, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                        · linarith only [h118, h120, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                          · linarith only [h118, h122, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                            · linarith only [h124, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · linarith only [h124, h88, hlam]
                    · linarith only [h104, h117, hlam, p0_1]
                  · linarith only [h116, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h115, hlam, p0_0]
              · linarith only [h114, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
    · linarith only [h67, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h132 | h132
    · rcases p0_3 (m.d 1 2) (by simp) with h133 | h133
      · rcases p0_3 (m.d 1 3) (by simp) with h134 | h134
        · rcases p0_3 (m.d 1 4) (by simp) with h135 | h135
          · linarith only [h135, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h137 | h137
            · rcases m.htr 0 1 2 (by decide) (by decide) with h138 | h138
              · linarith only [h133, h138, hlam]
              · linarith only [h138, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h133, h141, hlam]
              · linarith only [h141, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h144 | h144
          · linarith only [h144, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h146 | h146
            · rcases m.htr 0 1 2 (by decide) (by decide) with h147 | h147
              · linarith only [h133, h147, hlam]
              · linarith only [h134, h147, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h150 | h150
              · linarith only [h133, h150, hlam]
              · linarith only [h134, h150, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h153 | h153
        · rcases p0_3 (m.d 1 4) (by simp) with h154 | h154
          · linarith only [h154, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h156 | h156
            · rcases m.htr 0 1 2 (by decide) (by decide) with h157 | h157
              · rcases m.htr 0 1 3 (by decide) (by decide) with h158 | h158
                · linarith only [h153, h158, hlam]
                · linarith only [h133, h158, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h133, h157, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h162 | h162
              · rcases m.htr 0 1 3 (by decide) (by decide) with h163 | h163
                · linarith only [h153, h163, hlam]
                · linarith only [h133, h163, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h133, h162, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h167 | h167
          · linarith only [h167, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h169 | h169
            · rcases m.htr 0 1 2 (by decide) (by decide) with h170 | h170
              · rcases m.htr 0 1 3 (by decide) (by decide) with h171 | h171
                · rcases m.htr 0 1 4 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h169, h173, hlam]
                    · linarith only [h133, h173, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h172, hlam, p0_0]
                · linarith only [h153, h171, hlam, p0_1]
              · linarith only [h133, h170, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h179 | h179
              · rcases m.htr 0 1 3 (by decide) (by decide) with h180 | h180
                · rcases m.htr 0 1 4 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h182 | h182
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                      · linarith only [h133, h183, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
                        · linarith only [h133, h185, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h187 | h187
                          · linarith only [h153, h183, h187, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h189 | h189
                            · linarith only [h153, h189, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
                              · linarith only [h189, h191, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h193 | h193
                                · linarith only [h193, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                                · linarith only [h169, h193, hlam]
                    · linarith only [h182, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo4]
                  · linarith only [h181, hlam, p0_0]
                · linarith only [h180, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h133, h179, hlam, p0_1]
    · linarith only [h132, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h201 | h201
    · rcases p0_3 (m.d 1 2) (by simp) with h202 | h202
      · rcases p0_3 (m.d 1 3) (by simp) with h203 | h203
        · rcases p0_3 (m.d 1 4) (by simp) with h204 | h204
          · rcases p0_3 (m.d 1 5) (by simp) with h205 | h205
            · linarith only [h205, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h207 | h207
              · linarith only [h202, h207, hlam]
              · linarith only [h207, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h210 | h210
            · linarith only [h210, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h212 | h212
              · linarith only [h202, h212, hlam]
              · linarith only [h204, h212, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
        · rcases p0_3 (m.d 1 4) (by simp) with h215 | h215
          · rcases p0_3 (m.d 1 5) (by simp) with h216 | h216
            · linarith only [h216, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h218 | h218
              · linarith only [h202, h218, hlam]
              · linarith only [h203, h218, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h221 | h221
            · linarith only [h221, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h223 | h223
              · linarith only [h202, h223, hlam]
              · linarith only [h203, h223, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
      · rcases p0_3 (m.d 1 3) (by simp) with h226 | h226
        · rcases p0_3 (m.d 1 4) (by simp) with h227 | h227
          · rcases p0_3 (m.d 1 5) (by simp) with h228 | h228
            · linarith only [h228, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h230 | h230
              · rcases m.htr 0 1 3 (by decide) (by decide) with h231 | h231
                · linarith only [h226, h231, hlam]
                · linarith only [h202, h231, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h202, h230, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h235 | h235
            · linarith only [h235, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h237 | h237
              · rcases m.htr 0 1 3 (by decide) (by decide) with h238 | h238
                · linarith only [h226, h238, hlam]
                · linarith only [h202, h238, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h202, h237, hlam, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
          · rcases p0_3 (m.d 1 5) (by simp) with h243 | h243
            · linarith only [h243, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h245 | h245
              · rcases m.htr 0 1 3 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 1 4 (by decide) (by decide) with h247 | h247
                  · linarith only [h242, h247, hlam]
                  · linarith only [h202, h247, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h226, h246, hlam, p0_1]
              · linarith only [h202, h245, hlam, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h252 | h252
            · linarith only [h252, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h254 | h254
              · rcases m.htr 0 1 3 (by decide) (by decide) with h255 | h255
                · rcases m.htr 0 1 4 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
                      · linarith only [h202, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                        · linarith only [h226, h258, h260, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                          · linarith only [h202, h262, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                            · linarith only [h226, h264, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h266 | h266
                              · linarith only [h226, h266, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                                · linarith only [h242, h268, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                                  · linarith only [h258, h264, h270, hc12, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                                    · linarith only [h258, h264, h268, h272, hc12, hlam, hphi, u2elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                                      · linarith only [h260, h272, h274, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h258, h270, h274, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h257, hlam, p0_0]
                  · linarith only [h256, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3]
                · linarith only [h242, h255, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h202, h254, hlam, p0_1]
    · linarith only [h201, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h284 | h284
    · rcases p0_3 (m.d 1 2) (by simp) with h285 | h285
      · rcases p0_3 (m.d 1 3) (by simp) with h286 | h286
        · linarith only [h286, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h288 | h288
          · rcases p0_3 (m.d 1 5) (by simp) with h289 | h289
            · rcases m.htr 0 1 2 (by decide) (by decide) with h290 | h290
              · linarith only [h290, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h284, h290, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h293 | h293
              · linarith only [h293, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h284, h293, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h296 | h296
            · rcases m.htr 0 1 2 (by decide) (by decide) with h297 | h297
              · linarith only [h297, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h284, h297, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h300 | h300
              · linarith only [h300, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h284, h300, hlam]
      · linarith only [h285, hlam, p0_0]
    · linarith only [h284, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h305 | h305
    · rcases p0_3 (m.d 1 2) (by simp) with h306 | h306
      · rcases p0_3 (m.d 1 3) (by simp) with h307 | h307
        · rcases p0_3 (m.d 1 4) (by simp) with h308 | h308
          · linarith only [h308, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h310 | h310
            · rcases m.htr 0 1 2 (by decide) (by decide) with h311 | h311
              · linarith only [h311, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h305, h311, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h314 | h314
              · linarith only [h314, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h305, h314, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h317 | h317
          · linarith only [h317, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h319 | h319
            · rcases m.htr 0 1 2 (by decide) (by decide) with h320 | h320
              · linarith only [h307, h320, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h305, h320, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h323 | h323
              · linarith only [h307, h323, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h305, h323, hlam]
      · linarith only [h306, hlam, p0_0]
    · linarith only [h305, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h328 | h328
    · rcases p0_3 (m.d 1 2) (by simp) with h329 | h329
      · rcases p0_3 (m.d 1 3) (by simp) with h330 | h330
        · rcases p0_3 (m.d 1 4) (by simp) with h331 | h331
          · rcases p0_3 (m.d 1 5) (by simp) with h332 | h332
            · linarith only [h332, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · linarith only [h334, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h328, h334, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h337 | h337
            · linarith only [h337, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h339 | h339
              · linarith only [h331, h339, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h328, h339, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h342 | h342
          · rcases p0_3 (m.d 1 5) (by simp) with h343 | h343
            · linarith only [h343, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h345 | h345
              · linarith only [h330, h345, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h328, h345, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h348 | h348
            · linarith only [h348, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h350 | h350
              · linarith only [h330, h350, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h328, h350, hlam]
      · linarith only [h329, hlam, p0_0]
    · linarith only [h328, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h356 | h356
    · rcases p0_3 (m.d 1 2) (by simp) with h357 | h357
      · linarith only [h357, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h359 | h359
        · rcases p0_3 (m.d 1 4) (by simp) with h360 | h360
          · rcases p0_3 (m.d 1 5) (by simp) with h361 | h361
            · rcases m.htr 0 1 2 (by decide) (by decide) with h362 | h362
              · rcases m.htr 0 1 3 (by decide) (by decide) with h363 | h363
                · linarith only [h363, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h356, h363, hlam]
              · linarith only [h362, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h367 | h367
              · rcases m.htr 0 1 3 (by decide) (by decide) with h368 | h368
                · linarith only [h368, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h356, h368, hlam]
              · linarith only [h367, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h372 | h372
            · rcases m.htr 0 1 2 (by decide) (by decide) with h373 | h373
              · rcases m.htr 0 1 3 (by decide) (by decide) with h374 | h374
                · linarith only [h374, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h356, h374, hlam]
              · linarith only [h373, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h378 | h378
              · rcases m.htr 0 1 3 (by decide) (by decide) with h379 | h379
                · linarith only [h379, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h356, h379, hlam]
              · linarith only [h378, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h359, hlam, p0_0]
    · linarith only [h356, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h386 | h386
    · rcases p0_3 (m.d 1 2) (by simp) with h387 | h387
      · rcases p0_3 (m.d 1 3) (by simp) with h388 | h388
        · rcases p0_3 (m.d 1 4) (by simp) with h389 | h389
          · linarith only [h389, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h391 | h391
            · rcases m.htr 0 1 2 (by decide) (by decide) with h392 | h392
              · linarith only [h387, h392, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h386, h392, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h395 | h395
              · linarith only [h387, h395, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h386, h395, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h388, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h399 | h399
        · rcases p0_3 (m.d 1 4) (by simp) with h400 | h400
          · linarith only [h400, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h402 | h402
            · rcases m.htr 0 1 2 (by decide) (by decide) with h403 | h403
              · rcases m.htr 0 1 3 (by decide) (by decide) with h404 | h404
                · linarith only [h387, h404, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h386, h404, hlam]
              · linarith only [h387, h403, hc01, hlam, hphi, p0_1, u1elo2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 1 3 (by decide) (by decide) with h409 | h409
                · linarith only [h387, h409, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h386, h409, hlam]
              · linarith only [h387, h408, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h399, hlam, p0_0]
    · linarith only [h386, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h415 | h415
    · rcases p0_3 (m.d 1 2) (by simp) with h416 | h416
      · rcases p0_3 (m.d 1 3) (by simp) with h417 | h417
        · rcases p0_3 (m.d 1 4) (by simp) with h418 | h418
          · rcases p0_3 (m.d 1 5) (by simp) with h419 | h419
            · linarith only [h419, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h421 | h421
              · linarith only [h416, h421, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
              · linarith only [h415, h421, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
          · rcases p0_3 (m.d 1 5) (by simp) with h424 | h424
            · linarith only [h424, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h426 | h426
              · linarith only [h416, h418, h426, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h415, h418, h426, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo1]
        · linarith only [h417, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h430 | h430
        · rcases p0_3 (m.d 1 4) (by simp) with h431 | h431
          · rcases p0_3 (m.d 1 5) (by simp) with h432 | h432
            · linarith only [h432, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h434 | h434
              · rcases m.htr 0 1 3 (by decide) (by decide) with h435 | h435
                · linarith only [h416, h435, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h415, h435, hlam]
              · linarith only [h416, h434, hc01, hlam, hphi, p0_1, u1elo2]
          · rcases p0_3 (m.d 1 5) (by simp) with h439 | h439
            · linarith only [h439, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 1 3 (by decide) (by decide) with h442 | h442
                · linarith only [h416, h442, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h415, h442, hlam]
              · linarith only [h416, h441, hc01, hlam, hphi, p0_1, u1elo2]
        · linarith only [h430, hlam, p0_0]
    · linarith only [h415, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h449 | h449
    · rcases p0_3 (m.d 1 2) (by simp) with h450 | h450
      · linarith only [h450, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h452 | h452
        · rcases p0_3 (m.d 1 4) (by simp) with h453 | h453
          · rcases p0_3 (m.d 1 5) (by simp) with h454 | h454
            · rcases m.htr 0 1 2 (by decide) (by decide) with h455 | h455
              · rcases m.htr 0 1 3 (by decide) (by decide) with h456 | h456
                · linarith only [h452, h456, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h449, h456, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h449, h455, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h460 | h460
              · rcases m.htr 0 1 3 (by decide) (by decide) with h461 | h461
                · linarith only [h452, h461, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h449, h461, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h449, h460, hlam, p0_1]
          · linarith only [h453, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h466 | h466
          · rcases p0_3 (m.d 1 5) (by simp) with h467 | h467
            · rcases m.htr 0 1 2 (by decide) (by decide) with h468 | h468
              · rcases m.htr 0 1 3 (by decide) (by decide) with h469 | h469
                · rcases m.htr 0 1 4 (by decide) (by decide) with h470 | h470
                  · linarith only [h470, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h449, h470, hlam]
                · linarith only [h452, h469, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h449, h468, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 1 3 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 1 4 (by decide) (by decide) with h477 | h477
                  · linarith only [h477, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h449, h477, hlam]
                · linarith only [h452, h476, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h449, h475, hlam, p0_1]
          · linarith only [h466, hlam, p0_0]
    · linarith only [h449, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h484 | h484
    · rcases p0_3 (m.d 1 2) (by simp) with h485 | h485
      · rcases p0_3 (m.d 1 3) (by simp) with h486 | h486
        · linarith only [h486, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h488 | h488
          · rcases p0_3 (m.d 1 5) (by simp) with h489 | h489
            · rcases m.htr 0 1 2 (by decide) (by decide) with h490 | h490
              · linarith only [h485, h490, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h484, h490, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h493 | h493
              · linarith only [h485, h493, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h484, h493, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
          · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h497 | h497
        · linarith only [h497, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h499 | h499
          · rcases p0_3 (m.d 1 5) (by simp) with h500 | h500
            · rcases m.htr 0 1 2 (by decide) (by decide) with h501 | h501
              · rcases m.htr 0 1 3 (by decide) (by decide) with h502 | h502
                · rcases m.htr 0 1 4 (by decide) (by decide) with h503 | h503
                  · linarith only [h485, h503, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h484, h503, hlam]
                · linarith only [h502, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h484, h501, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h508 | h508
              · rcases m.htr 0 1 3 (by decide) (by decide) with h509 | h509
                · rcases m.htr 0 1 4 (by decide) (by decide) with h510 | h510
                  · linarith only [h485, h510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h484, h510, hlam]
                · linarith only [h509, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h484, h508, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h499, hlam, p0_0]
    · linarith only [h484, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h518 | h518
    · rcases p0_3 (m.d 1 2) (by simp) with h519 | h519
      · rcases p0_3 (m.d 1 3) (by simp) with h520 | h520
        · rcases p0_3 (m.d 1 4) (by simp) with h521 | h521
          · rcases p0_3 (m.d 1 5) (by simp) with h522 | h522
            · linarith only [h522, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h524 | h524
              · linarith only [h519, h524, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
              · linarith only [h518, h524, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo1]
          · linarith only [h521, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h528 | h528
          · rcases p0_3 (m.d 1 5) (by simp) with h529 | h529
            · linarith only [h529, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h531 | h531
              · linarith only [h519, h520, h531, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h518, h520, h531, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h535 | h535
        · rcases p0_3 (m.d 1 4) (by simp) with h536 | h536
          · rcases p0_3 (m.d 1 5) (by simp) with h537 | h537
            · linarith only [h537, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h539 | h539
              · rcases m.htr 0 1 3 (by decide) (by decide) with h540 | h540
                · linarith only [h519, h535, h540, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h518, h519, h540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h518, h519, h539, hlam, p0_1]
          · linarith only [h536, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h545 | h545
          · rcases p0_3 (m.d 1 5) (by simp) with h546 | h546
            · linarith only [h546, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h548 | h548
              · rcases m.htr 0 1 3 (by decide) (by decide) with h549 | h549
                · rcases m.htr 0 1 4 (by decide) (by decide) with h550 | h550
                  · linarith only [h519, h550, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h518, h550, hlam]
                · linarith only [h535, h549, hc01, hlam, hphi, p0_1, u1elo3]
              · linarith only [h518, h535, h548, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
          · linarith only [h545, hlam, p0_0]
    · linarith only [h518, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h558 | h558
    · rcases p0_3 (m.d 1 2) (by simp) with h559 | h559
      · linarith only [h559, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h561 | h561
        · rcases p0_3 (m.d 1 4) (by simp) with h562 | h562
          · rcases p0_3 (m.d 1 5) (by simp) with h563 | h563
            · rcases m.htr 0 1 2 (by decide) (by decide) with h564 | h564
              · rcases m.htr 0 1 3 (by decide) (by decide) with h565 | h565
                · linarith only [h561, h565, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h558, h565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h558, h564, hlam, p0_1]
            · linarith only [h563, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h570 | h570
            · rcases m.htr 0 1 2 (by decide) (by decide) with h571 | h571
              · rcases m.htr 0 1 3 (by decide) (by decide) with h572 | h572
                · linarith only [h561, h572, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h558, h572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h558, h571, hlam, p0_1]
            · linarith only [h570, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h577 | h577
          · rcases p0_3 (m.d 1 5) (by simp) with h578 | h578
            · rcases m.htr 0 1 2 (by decide) (by decide) with h579 | h579
              · rcases m.htr 0 1 3 (by decide) (by decide) with h580 | h580
                · rcases m.htr 0 1 4 (by decide) (by decide) with h581 | h581
                  · linarith only [h577, h581, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h558, h581, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h558, h561, h580, hlam, p0_1]
              · linarith only [h558, h579, hlam, p0_1]
            · linarith only [h578, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h587 | h587
            · rcases m.htr 0 1 2 (by decide) (by decide) with h588 | h588
              · rcases m.htr 0 1 3 (by decide) (by decide) with h589 | h589
                · rcases m.htr 0 1 4 (by decide) (by decide) with h590 | h590
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h591 | h591
                    · linarith only [h591, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h558, h591, hlam]
                  · linarith only [h577, h590, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h558, h561, h589, hlam, p0_1]
              · linarith only [h558, h588, hlam, p0_1]
            · linarith only [h587, hlam, p0_0]
    · linarith only [h558, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h599 | h599
    · rcases p0_3 (m.d 1 2) (by simp) with h600 | h600
      · rcases p0_3 (m.d 1 3) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h603 | h603
          · rcases p0_3 (m.d 1 5) (by simp) with h604 | h604
            · rcases m.htr 0 1 2 (by decide) (by decide) with h605 | h605
              · linarith only [h600, h605, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h599, h605, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h604, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h609 | h609
            · rcases m.htr 0 1 2 (by decide) (by decide) with h610 | h610
              · linarith only [h600, h610, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
              · linarith only [h599, h610, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
            · linarith only [h609, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h614 | h614
        · linarith only [h614, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h616 | h616
          · rcases p0_3 (m.d 1 5) (by simp) with h617 | h617
            · rcases m.htr 0 1 2 (by decide) (by decide) with h618 | h618
              · rcases m.htr 0 1 3 (by decide) (by decide) with h619 | h619
                · rcases m.htr 0 1 4 (by decide) (by decide) with h620 | h620
                  · linarith only [h600, h616, h620, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                  · linarith only [h599, h600, h620, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo3]
                · linarith only [h599, h619, hlam, p0_1]
              · linarith only [h599, h600, h618, hlam, p0_1]
            · linarith only [h617, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h626 | h626
            · rcases m.htr 0 1 2 (by decide) (by decide) with h627 | h627
              · rcases m.htr 0 1 3 (by decide) (by decide) with h628 | h628
                · rcases m.htr 0 1 4 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h630 | h630
                    · linarith only [h600, h630, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h599, h630, hlam]
                  · linarith only [h616, h629, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h599, h628, hlam, p0_1]
              · linarith only [h599, h627, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h626, hlam, p0_0]
    · linarith only [h599, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h638 | h638
    · rcases p0_3 (m.d 1 2) (by simp) with h639 | h639
      · rcases p0_3 (m.d 1 3) (by simp) with h640 | h640
        · rcases p0_3 (m.d 1 4) (by simp) with h641 | h641
          · linarith only [h641, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h643 | h643
            · rcases m.htr 0 1 2 (by decide) (by decide) with h644 | h644
              · linarith only [h639, h644, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h638, h644, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
            · linarith only [h643, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h648 | h648
          · linarith only [h648, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h650 | h650
            · rcases m.htr 0 1 2 (by decide) (by decide) with h651 | h651
              · linarith only [h639, h640, h651, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo0]
              · linarith only [h638, h640, h651, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
            · linarith only [h650, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h655 | h655
        · rcases p0_3 (m.d 1 4) (by simp) with h656 | h656
          · linarith only [h656, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h658 | h658
            · rcases m.htr 0 1 2 (by decide) (by decide) with h659 | h659
              · rcases m.htr 0 1 3 (by decide) (by decide) with h660 | h660
                · linarith only [h639, h655, h660, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                · linarith only [h638, h639, h660, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo2]
              · linarith only [h638, h639, h659, hlam, p0_1]
            · linarith only [h658, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h665 | h665
          · linarith only [h665, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h667 | h667
            · rcases m.htr 0 1 2 (by decide) (by decide) with h668 | h668
              · rcases m.htr 0 1 3 (by decide) (by decide) with h669 | h669
                · rcases m.htr 0 1 4 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h671 | h671
                    · linarith only [h639, h671, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
                    · linarith only [h638, h671, hlam]
                  · linarith only [h670, hc01, hlam, hphi, p0_1, u1elo4]
                · linarith only [h638, h655, h669, hlam, p0_1]
              · linarith only [h638, h655, h668, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u1elo1]
            · linarith only [h667, hlam, p0_0]
    · linarith only [h638, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
