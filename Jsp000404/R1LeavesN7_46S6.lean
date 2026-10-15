import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5996000 in
set_option maxHeartbeats 5996000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h11, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h11, h17, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h11, h12, h2, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h11, h21, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                              · linarith only [h0, h11, h2, h24, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · linarith only [h21, h26, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                    · rcases h0bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h21, h29, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h21, h29, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h21, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h21, h29, h5, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h21, h29, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h21, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h1, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h2, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h21, h29, h5, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h2, h21, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h3, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h5, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h2, h21, h5, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi2]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h4, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h6, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h7, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                    · linarith only [h0, h28, h29, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h23, h28, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                              · linarith only [h0, h11, h2, h23, h5, h58, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                · linarith only [h0, h11, h2, h23, h5, h60, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                  · linarith only [h11, h23, h62, h8, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                                    · linarith only [h11, h23, h64, h8, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h0, h11, h2, h5, h64, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h10, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                    · linarith only [h69, h8, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h2, h71, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                                    · rcases h0bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h2, h71, h76, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h1, h73, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p80_1, u3ehi4]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h3, h71, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h4, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h2, h71, h76, h78, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, h3, h71, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, h4, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h1, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h2, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h3, h71, h78, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, h2, h4, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h3, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h5, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h4, h5, h71, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u2ehi1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h4, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h6, hlam, p80_0]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [h7, hlam, p80_1]
                                      · have p80_0 := h80c.1
                                        have p80_1 := h80c.2.1
                                        have p80_2 := h80c.2.2.1
                                        have p80_3 := h80c.2.2.2
                                        linarith only [hlam, p80_0]
                                    · linarith only [h0, h2, h69, h75, h76, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h69, h75, h78, hlam]
                                · linarith only [h0, h2, h6, h77, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h73, h76, h8, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                                  · linarith only [h0, h112, h3, h69, h75, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h112, h69, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h0, h111, h2, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h110, h73, h8, hlam]
                          · linarith only [h73, h74, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                          · linarith only [h0, h118, h2, h5, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                              · linarith only [h0, h121, h2, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h121, h5, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                              · linarith only [h124, h73, h8, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h124, h2, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h0, h128, h132, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                              · linarith only [h0, h127, h134, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h130, h134, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h130, h131, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h130, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h0, h127, h129, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h127, h128, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                    · linarith only [h127, h141, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h141, h3, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
              · linarith only [h145, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
                · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                        · linarith only [h1, h151, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                          · linarith only [h1, h145, h153, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                              · linarith only [h1, h148, h156, h5, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                · linarith only [h1, h145, h148, h158, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                                    · rcases h0bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h0, h149, h160, hc01, hc45, hlam, hphi, ht0b, ht5b, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h165 | h165
                                        · rcases p162_3 (m.d 0 2) (by simp) with h166 | h166
                                          · linarith only [h0, h166, hlam]
                                          · linarith only [h166, h2, hlam]
                                        · linarith only [h1, h165, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h170 | h170
                                        · rcases p162_3 (m.d 0 2) (by simp) with h171 | h171
                                          · linarith only [h0, h171, hlam]
                                          · linarith only [h171, h3, hlam]
                                        · linarith only [h170, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h175 | h175
                                        · rcases p162_3 (m.d 0 2) (by simp) with h176 | h176
                                          · linarith only [h0, h176, hlam]
                                          · linarith only [h176, h4, hlam]
                                        · linarith only [h175, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h0, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h182 | h182
                                        · rcases p162_3 (m.d 0 2) (by simp) with h183 | h183
                                          · rcases p162_3 (m.d 0 3) (by simp) with h184 | h184
                                            · linarith only [h184, h2, hlam]
                                            · rcases p162_3 (m.d 0 4) (by simp) with h186 | h186
                                              · linarith only [h186, h3, hlam]
                                              · linarith only [h186, h5, hlam]
                                          · linarith only [h183, h2, hlam]
                                        · linarith only [h1, h182, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h191 | h191
                                        · rcases p162_3 (m.d 0 2) (by simp) with h192 | h192
                                          · rcases p162_3 (m.d 0 3) (by simp) with h193 | h193
                                            · linarith only [h193, h2, hlam]
                                            · rcases p162_3 (m.d 0 4) (by simp) with h195 | h195
                                              · linarith only [h195, h3, hlam]
                                              · rcases p162_3 (m.d 0 5) (by simp) with h197 | h197
                                                · linarith only [h197, h4, hlam]
                                                · rcases h0emin with h199 | h199 | h199 | h199 | h199
                                                  · rcases h3bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h145, h147, h148, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h0, h145, h147, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h5, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h145, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h1, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h151, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h153, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h2, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h148, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h156, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h158, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hc34, hlam, hphi, p200_1, u3ehi0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h148, hc34, hlam, hphi, ht23, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hc34, hlam, hphi, ht23, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h1, h145, h148, hc34, hlam, hphi, ht23, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h1, h148, hc35, hlam, hphi, ht23, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h148, hc35, hlam, hphi, ht23, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hc35, hlam, hphi, ht23, p200_1, u2ehi2]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [h161, hlam, p200_0]
                                                    · have p200_0 := h200c.1
                                                      have p200_1 := h200c.2.1
                                                      have p200_2 := h200c.2.2.1
                                                      have p200_3 := h200c.2.2.2
                                                      linarith only [hlam, p200_0]
                                                  · rcases h3bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h0, h145, h147, h148, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h0, h145, h147, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h5, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h145, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h1, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h151, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h153, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h2, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h148, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h156, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h158, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hc34, hlam, hphi, p226_1, u3ehi0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h148, hc34, hlam, hphi, ht23, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hc34, hlam, hphi, ht23, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hc34, hlam, hphi, p226_1, u3ehi4]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h1, h148, hc35, hlam, hphi, ht23, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h148, hc35, hlam, hphi, ht23, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hc35, hlam, hphi, ht23, p226_1, u2ehi2]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [h161, hlam, p226_0]
                                                    · have p226_0 := h226c.1
                                                      have p226_1 := h226c.2.1
                                                      have p226_2 := h226c.2.2.1
                                                      have p226_3 := h226c.2.2.2
                                                      linarith only [hlam, p226_0]
                                                  · linarith only [h199, h5, hc34, hlam, ht01, ht12, ht23]
                                                  · linarith only [h0, h199, hc01, hlam, p162_1]
                                                  · linarith only [h0, h147, h199, hc01, hlam, p162_1]
                                          · linarith only [h192, h3, hlam]
                                        · linarith only [h0, h191, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        rcases p162_3 (m.d 0 1) (by simp) with h257 | h257
                                        · rcases p162_3 (m.d 0 2) (by simp) with h258 | h258
                                          · rcases p162_3 (m.d 0 3) (by simp) with h259 | h259
                                            · linarith only [h2, h259, hlam]
                                            · rcases p162_3 (m.d 0 4) (by simp) with h261 | h261
                                              · linarith only [h261, h3, hlam]
                                              · linarith only [h147, h261, hlam]
                                          · linarith only [h258, h4, hlam]
                                        · linarith only [h0, h147, h257, h3, hlam]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h1, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h2, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h5, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h145, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h0, h149, h158, h160, h5, hc34, hlam, hphi, ht23, p162_1, u2ehi2]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h3, hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h5, hc34, hlam, hphi, p162_1, u3ehi0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h158, h4, h5, hc34, hlam, hphi, ht23, p162_1, u2ehi2]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h0, h149, h158, h160, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u2ehi2]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h4, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h1, h145, h148, h161, hc34, hlam, hphi, ht23, p162_1, u2ehi2]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [h147, hlam, p162_1]
                                      · have p162_0 := h162c.1
                                        have p162_1 := h162c.2.1
                                        have p162_2 := h162c.2.2.1
                                        have p162_3 := h162c.2.2.2
                                        linarith only [hlam, p162_0]
                                    · linarith only [h1, h148, h161, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                  · linarith only [h147, h160, h5, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h147, h149, h155, h5, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h149, h150, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h148, h149, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h148, h2, h5, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                        · linarith only [h1, h147, h290, h5, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                          · linarith only [h1, h145, h292, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h294 | h294
                            · linarith only [h0, h147, h288, h294, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                              · linarith only [h1, h287, h296, h5, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h298 | h298
                                · linarith only [h1, h145, h287, h298, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h300 | h300
                                  · linarith only [h147, h3, h300, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h302 | h302
                                    · linarith only [h147, h3, h302, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h1, h287, h302, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h287, h289, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h287, h288, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h2, h287, h5, hc34, hlam, hphi, ht23, u2ehi1]
          · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h310 | h310
        · linarith only [h2, h310, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h312 | h312
          · linarith only [h2, h312, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h314 | h314
            · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
              · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                  · linarith only [h0, h2, h317, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                    · linarith only [h0, h310, h319, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                      · linarith only [h0, h312, h321, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h323 | h323
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h324 | h324
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h328 | h328
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                                    · rcases h0bigk with h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        rcases p330_3 (m.d 0 1) (by simp) with h332 | h332
                                        · rcases p330_3 (m.d 0 2) (by simp) with h333 | h333
                                          · linarith only [h0, h333, hlam]
                                          · rcases p330_3 (m.d 0 3) (by simp) with h335 | h335
                                            · linarith only [h1, h335, hlam]
                                            · linarith only [h2, h335, hlam]
                                        · linarith only [h0, h332, hlam]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h1, h323, h329, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p330_1, u3ehi4]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        rcases p330_3 (m.d 0 1) (by simp) with h340 | h340
                                        · rcases p330_3 (m.d 0 2) (by simp) with h341 | h341
                                          · linarith only [h0, h341, hlam]
                                          · rcases p330_3 (m.d 0 3) (by simp) with h343 | h343
                                            · linarith only [h1, h343, hlam]
                                            · linarith only [h314, h343, hlam]
                                        · linarith only [h340, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        rcases p330_3 (m.d 0 1) (by simp) with h347 | h347
                                        · rcases p330_3 (m.d 0 2) (by simp) with h348 | h348
                                          · linarith only [h0, h348, hlam]
                                          · rcases p330_3 (m.d 0 3) (by simp) with h350 | h350
                                            · linarith only [h1, h350, hlam]
                                            · linarith only [h315, h350, hlam]
                                        · linarith only [h347, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h2, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h310, hlam, p330_1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h312, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h1, hlam, p330_1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, h2, hc23, hlam, hphi, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, h2, h312, h316, hc23, hlam, hphi, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, h2, h312, hc23, hlam, hphi, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, h310, hc24, hlam, hphi, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h314, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, h2, h312, h314, hc23, hlam, hphi, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h1, h323, h329, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p330_1, u3ehi4]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h0, h312, hc25, hlam, hphi, p330_1, u2ehi1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h315, hlam, p330_0]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [h316, hlam, p330_1]
                                      · have p330_0 := h330c.1
                                        have p330_1 := h330c.2.1
                                        have p330_2 := h330c.2.2.1
                                        have p330_3 := h330c.2.2.2
                                        linarith only [hlam, p330_0]
                                    · linarith only [h1, h323, h325, h329, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h1, h323, h325, h328, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h2, h327, hc35, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h0, h2, h326, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h2, h314, h316, h319, h325, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h323, h324, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h2, h314, h317, h323, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                  · linarith only [h0, h310, h381, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                    · linarith only [h0, h310, h316, h383, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h385 | h385
                      · linarith only [h0, h310, h316, h385, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                            · linarith only [h310, h316, h383, h389, hc24, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
                                  · linarith only [h0, h310, h316, h391, h393, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h310, h393, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h0, h2, h392, hc35, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h1, h2, h388, h391, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h387, h388, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h314, h316, h387, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h314, h315, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h401 | h401
              · linarith only [h314, h401, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                  · linarith only [h0, h2, h404, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
                    · linarith only [h0, h310, h406, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h408 | h408
                      · linarith only [h0, h2, h408, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                        · linarith only [h1, h314, h410, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h412 | h412
                          · linarith only [h1, h401, h412, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h414 | h414
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                              · linarith only [h2, h314, h415, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h2, h415, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h314, h403, h406, h414, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                  · linarith only [h0, h2, h419, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                    · linarith only [h0, h2, h421, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                      · linarith only [h0, h312, h423, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                        · linarith only [h1, h314, h403, h425, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h427 | h427
                          · linarith only [h1, h314, h403, h427, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                            · linarith only [h2, h314, h403, h421, h429, hc24, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h431 | h431
                              · linarith only [h0, h2, h314, h431, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h2, h431, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h434 | h434
      · linarith only [h0, h1, h434, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h436 | h436
        · linarith only [h434, h436, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h438 | h438
          · linarith only [h434, h438, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h440 | h440
            · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
              · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                  · linarith only [h0, h1, h434, h443, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h0, h1, h443, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                  · linarith only [h0, h1, h446, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1, h446, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h441, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h440, hc34, hlam, hphi, ht23, u2ehi1]
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0 m hb0 hb2 hb3 h0

end R2N4
