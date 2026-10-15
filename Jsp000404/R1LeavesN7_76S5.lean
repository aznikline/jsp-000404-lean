import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_IR_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h11, h13, h9, hlam]
                          · rcases h0bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h2, h5, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h5, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hc01, hlam, hphi, p15_1, u0ehi4]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h5, h7, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h11, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p15_1, u0ehi4]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h8, hc03, hlam, hphi, ht0b, ht45, ht5b, p15_1, u4ehi1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h2, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h11, h2, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h11, h2, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h1, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h3, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h5, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h11, h7, h9, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi3]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h0, h8, hc05, hlam, hphi, ht0b, ht45, ht5b, p15_1, u4ehi1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h4, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h6, hlam, p15_0]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [h7, hlam, p15_1]
                            · have p15_0 := h15c.1
                              have p15_1 := h15c.2.1
                              have p15_2 := h15c.2.2.1
                              have p15_3 := h15c.2.2.2
                              linarith only [hlam, p15_0]
                      · linarith only [h0, h10, h2, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h42, h9, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h0, h44, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h2, h44, h46, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h46, h7, h9, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                          · linarith only [h0, h2, h49, h52, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h2, h49, h51, h52, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h51, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                      · linarith only [h49, h50, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h0, h2, h49, h5, h57, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                          · rcases h0bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h2, h49, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p61_1, u1ehi1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h49, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p61_1, u1ehi1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc01, hlam, hphi, p61_1, u0ehi3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h57, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p61_1, u3ehi2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h49, h5, h8, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p61_1, u1ehi1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h49, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p61_1, u1ehi1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h57, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p61_1, u3ehi2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc03, hlam, hphi, p61_1, u0ehi0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h2, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h2, h49, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p61_1, u1ehi1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h2, h57, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p61_1, u3ehi2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h3, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h5, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h57, h6, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p61_1, u3ehi2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc05, hlam, hphi, p61_1, u0ehi0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h4, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h6, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h7, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                          · linarith only [h49, h59, h60, hlam]
                        · linarith only [h59, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h7, h89, h92, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                          · linarith only [h7, h94, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · rcases h0bigk with h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h2, h91, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u3ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hc01, hlam, hphi, p96_1, u0ehi2]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hc01, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h7, hc01, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h0, hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h2, h91, h94, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u3ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h0, h7, hc01, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hc03, hlam, hphi, p96_1, u0ehi0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h2, hlam, p96_1]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h0, h2, hc01, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h0, h2, h7, hc01, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h1, hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h3, hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h5, hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h7, hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hc05, hlam, hphi, p96_1, u0ehi0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h4, hlam, p96_1]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [h6, hlam, p96_0]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hc05, hlam, hphi, p96_1, u0ehi3]
                            · have p96_0 := h96c.1
                              have p96_1 := h96c.2.1
                              have p96_2 := h96c.2.2.1
                              have p96_3 := h96c.2.2.2
                              linarith only [hlam, p96_0]
                      · linarith only [h0, h2, h6, h90, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h5, h7, h90, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h3, h7, h89, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h126 | h126
              · linarith only [h126, h5, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                    · linarith only [h130, h5, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h126, h129, h130, h132, hc12, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                        · linarith only [h0, h129, h134, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h128, h130, h134, h5, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                    · linarith only [h0, h137, h2, h5, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                      · linarith only [h126, h139, h2, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                          · rcases h0bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hc01, hlam, hphi, p143_1, u0ehi1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hc01, hlam, hphi, p143_1, u0ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h129, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h126, hc01, hlam, hphi, p143_1, u0ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hc02, hlam, hphi, p143_1, u0ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, h129, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, h126, hc01, hlam, hphi, p143_1, u0ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h126, h142, hc34, hlam, hphi, ht12, ht23, p143_1, u1ehi0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h2, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h5, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h126, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h1, hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h3, hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hc04, hlam, hphi, p143_1, u0ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, h126, h129, h3, h5, hc01, hc34, hlam, hphi, ht12, ht23, p143_1, u0ehi2, u1ehi1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, h129, h3, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h4, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hc05, hlam, hphi, p143_1, u0ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h128, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                          · linarith only [h0, h141, h142, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · linarith only [h129, h141, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                    · linarith only [h172, h5, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                      · linarith only [h0, h171, h172, h174, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                        · linarith only [h0, h128, h171, h176, h5, hc01, hlam, hphi, u0ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h178 | h178
                          · linarith only [h128, h178, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · linarith only [h178, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h128, h171, h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
            · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
              · linarith only [h183, h2, h4, hlam]
              · linarith only [h182, h183, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h186 | h186
              · linarith only [h182, h186, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h188 | h188
                · linarith only [h188, h3, h4, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                    · linarith only [h191, h2, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                      · linarith only [h186, h190, h191, h193, hc12, hlam, hphi, ht01, u0ehi4]
                      · linarith only [h0, h190, h191, h193, h4, hc35, hlam, hphi, u3ehi2]
                  · linarith only [h190, h3, h4, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h197 | h197
          · rcases m.htr 0 3 4 (by decide) (by decide) with h198 | h198
            · linarith only [h198, h2, h3, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
              · linarith only [h198, h200, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h202 | h202
                · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                  · linarith only [h203, h3, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                    · linarith only [h2, h205, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h2, h205, h3, hc34, hlam, hphi, u3ehi2]
                · linarith only [h2, h202, h3, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h209 | h209
            · linarith only [h2, h209, h3, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
              · linarith only [h209, h211, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                  · linarith only [h0, h214, h3, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                    · linarith only [h209, h216, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h2, h216, h3, hc34, hlam, hphi, u3ehi2]
                · linarith only [h2, h213, h3, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h220 | h220
        · rcases m.htr 0 2 5 (by decide) (by decide) with h221 | h221
          · rcases m.htr 0 3 4 (by decide) (by decide) with h222 | h222
            · rcases m.htr 0 3 5 (by decide) (by decide) with h223 | h223
              · rcases m.htr 0 4 5 (by decide) (by decide) with h224 | h224
                · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                        · linarith only [h0, h2, h225, h228, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h220, h224, h226, h228, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2, h227, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h0, h2, h225, h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h2, h220, h225, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                        · linarith only [h0, h2, h224, h234, h237, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                          · linarith only [h0, h2, h224, h234, h235, h239, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                          · rcases h0bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, h234, hc01, hlam, hphi, ht0b, ht45, ht5b, p241_1, u4ehi2]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc01, hlam, hphi, p241_1, u0ehi2]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc01, hlam, hphi, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h224, hc01, hlam, hphi, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h2, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h2, h224, hc23, hlam, hphi, ht01, ht12, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc03, hlam, hphi, p241_1, u0ehi0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc03, hlam, hphi, p241_1, u0ehi1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h2, h224, hc23, hlam, hphi, ht01, ht12, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h1, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h220, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h222, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h224, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, h234, h235, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p241_1, u3ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h221, hlam, p241_1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h223, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h221, hc02, hlam, hphi, p241_1, u0ehi3]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                      · linarith only [h2, h236, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h0, h2, h234, h235, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h2, h220, h234, hc12, hc23, hlam, hphi]
              · linarith only [h222, h223, hc35, hlam, hphi, u3ehi3]
            · linarith only [h2, h220, h222, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h272 | h272
            · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
              · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
                · linarith only [h220, h221, h274, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                        · linarith only [h0, h274, h276, h279, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · linarith only [h0, h221, h276, h277, h279, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h2, h273, h278, hlam]
                    · linarith only [h2, h273, h277, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h220, h221, h276, hc25, hlam, hphi, ht12, u1ehi1]
              · linarith only [h272, h273, hc35, hlam, hphi, u3ehi3]
            · linarith only [h2, h220, h272, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h287 | h287
          · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
            · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
              · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
                  · linarith only [h220, h287, h291, hc12, hlam, hphi, ht01, u0ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h293 | h293
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h294 | h294
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
                          · rcases h0bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h287, h294, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p297_1, u3ehi4]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h288, hc01, hlam, hphi, ht0b, ht45, ht5b, p297_1, u4ehi3]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hc01, hlam, hphi, p297_1, u0ehi3]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hc01, hlam, hphi, p297_1, u0ehi4]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h0, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h2, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h220, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hc02, hlam, hphi, p297_1, u0ehi4]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht12, p297_1, u1ehi0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p297_1, u0ehi1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p297_1, u0ehi3]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p297_1, u0ehi4]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h1, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h287, h294, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p297_1, u3ehi4]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h288, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h220, h293, hc23, hlam, hphi, ht01, ht12, p297_1, u0ehi4]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hc05, hlam, hphi, p297_1, u0ehi0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h287, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h289, hlam, p297_0]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [h290, hlam, p297_1]
                            · have p297_0 := h297c.1
                              have p297_1 := h297c.2.1
                              have p297_2 := h297c.2.2.1
                              have p297_3 := h297c.2.2.2
                              linarith only [hlam, p297_0]
                          · linarith only [h2, h287, h295, h296, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h220, h295, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h220, h287, h293, h294, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h2, h287, h293, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                · linarith only [h220, h287, h290, hlam]
              · linarith only [h288, h289, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
              · linarith only [h288, h329, hc34, hlam, hphi, u3ehi4]
              · linarith only [h2, h287, h329, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
            · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
              · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                · rcases m.htr 1 2 4 (by decide) (by decide) with h335 | h335
                  · linarith only [h220, h335, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                          · rcases h0bigk with h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hc01, hlam, hphi, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h332, h340, hc01, hlam, hphi, ht0b, ht45, ht5b, p341_1, u4ehi4]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hc01, hlam, hphi, p341_1, u0ehi3]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h287, hc01, hlam, hphi, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h0, hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h2, hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h220, hlam, p341_1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h287, hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hc03, hlam, hphi, p341_1, u0ehi0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h2, h332, h340, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p341_1, u4ehi4]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h2, h287, hc23, hlam, hphi, ht01, ht12, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h1, hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hc04, hlam, hphi, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h332, hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h2, h287, h332, hc23, hlam, hphi, ht01, ht12, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hc05, hlam, hphi, p341_1, u0ehi0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h287, hc25, hlam, hphi, ht01, ht12, p341_1, u0ehi1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h333, hlam, p341_0]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [h334, hlam, p341_1]
                            · have p341_0 := h341c.1
                              have p341_1 := h341c.2.1
                              have p341_2 := h341c.2.2.1
                              have p341_3 := h341c.2.2.2
                              linarith only [hlam, p341_0]
                          · rcases h0bigk with h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hc01, hlam, hphi, p367_1, u0ehi1]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hc01, hlam, hphi, p367_1, u0ehi2]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h334, hc01, hlam, hphi, p367_1, u0ehi4]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h334, h340, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p367_1, u3ehi3]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h0, hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h2, hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h220, hlam, p367_1]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h287, hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hc03, hlam, hphi, p367_1, u0ehi0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h2, hc23, hlam, hphi, ht01, ht12, p367_1, u0ehi1]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h2, h334, h340, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p367_1, u3ehi3]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h2, h334, h340, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p367_1, u3ehi3]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h1, hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, p367_1, u0ehi1]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h332, hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h220, h334, h337, h340, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p367_1, u3ehi3]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hc05, hlam, hphi, p367_1, u0ehi0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h287, h337, h339, hc23, hlam, hphi, ht01, ht12, p367_1, u0ehi1]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h333, hlam, p367_0]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [h334, hlam, p367_1]
                            · have p367_0 := h367c.1
                              have p367_1 := h367c.2.1
                              have p367_2 := h367c.2.2.1
                              have p367_3 := h367c.2.2.2
                              linarith only [hlam, p367_0]
                        · linarith only [h220, h339, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h2, h338, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h2, h333, h337, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                  · linarith only [h220, h396, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h400 | h400
                        · linarith only [h334, h398, h400, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                        · linarith only [h220, h400, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · linarith only [h2, h333, h399, hc03, hlam, hphi, u0ehi1]
                    · linarith only [h2, h333, h398, hc34, hlam, hphi, u3ehi4]
              · linarith only [h332, h333, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h406 | h406
              · linarith only [h332, h406, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
                · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
                  · linarith only [h0, h220, h409, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                    · linarith only [h332, h411, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h2, h411, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                  · linarith only [h220, h414, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                    · linarith only [h2, h332, h416, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2, h416, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h420 | h420
    · linarith only [h0, h420, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h422 | h422
      · rcases m.htr 0 2 4 (by decide) (by decide) with h423 | h423
        · rcases m.htr 0 2 5 (by decide) (by decide) with h424 | h424
          · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
            · rcases m.htr 0 3 5 (by decide) (by decide) with h426 | h426
              · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h430 | h430
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h431 | h431
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h432 | h432
                          · linarith only [h422, h429, h432, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h422, h429, h431, h432, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                          · linarith only [h429, h431, h435, hlam]
                          · rcases h0bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, hlam, p437_1]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h420, h425, h427, h428, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h420, hlam, p437_1]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h420, h427, h428, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p437_1, u1ehi0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, h425, h427, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, h427, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, h427, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hc03, hlam, hphi, p437_1, u0ehi0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h422, hlam, p437_1]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h427, h429, h431, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, h422, h427, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hc04, hlam, hphi, p437_1, u0ehi0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h423, hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h425, hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h0, h422, h425, h427, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p437_1, u3ehi3]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hc05, hlam, hphi, p437_1, u0ehi0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h424, hlam, p437_1]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h426, hlam, p437_0]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [h427, hlam, p437_1]
                            · have p437_0 := h437c.1
                              have p437_1 := h437c.2.1
                              have p437_2 := h437c.2.2.1
                              have p437_3 := h437c.2.2.2
                              linarith only [hlam, p437_0]
                      · linarith only [h0, h422, h426, h429, h430, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                      · linarith only [h429, h464, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                          · rcases h0bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h425, h464, h467, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1, u3ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h420, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h420, h428, hc12, hlam, hphi, ht01, p468_1, u0ehi4]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p468_1, u1ehi0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, h425, h464, h467, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1, u3ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p468_1, u0ehi3]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p468_1, u0ehi4]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hc03, hlam, hphi, p468_1, u0ehi0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h422, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, h422, h425, h464, h467, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1, u3ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, h422, h426, h464, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1, u3ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hc04, hlam, hphi, p468_1, u0ehi0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h423, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h425, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, h422, h425, h426, h464, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p468_1, u3ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hc05, hlam, hphi, p468_1, u0ehi0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h424, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h426, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h427, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                          · linarith only [h0, h423, h466, h467, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                          · linarith only [h0, h422, h425, h466, h495, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h429, h495, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h428, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h502 | h502
                        · linarith only [h423, h427, h502, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
                          · linarith only [h422, h427, h500, h504, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases h0bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, hlam, p506_1]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h420, h422, h427, hc45, hlam, hphi, ht34, p506_1, u3ehi2]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h420, hlam, p506_1]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h420, h427, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p506_1, u0ehi4]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p506_1, u1ehi0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p506_1, u0ehi2]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p506_1, u0ehi3]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p506_1, u0ehi4]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hc03, hlam, hphi, p506_1, u0ehi0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h422, hlam, p506_1]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, h420, h422, hc12, hlam, hphi, ht01, p506_1, u0ehi0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, h420, h422, h427, hc12, hlam, hphi, ht01, p506_1, u0ehi0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hc04, hlam, hphi, p506_1, u0ehi0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h423, hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h425, hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h427, hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h0, h422, h427, h501, h504, hc12, hc45, hlam, hphi, ht01, ht34, p506_1, u0ehi0, u3ehi3]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h424, hlam, p506_1]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h426, hlam, p506_0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [h427, hc45, hlam, hphi, p506_1, u4ehi0]
                            · have p506_0 := h506c.1
                              have p506_1 := h506c.2.1
                              have p506_2 := h506c.2.2.1
                              have p506_3 := h506c.2.2.2
                              linarith only [hlam, p506_0]
                      · linarith only [h0, h422, h426, h500, h501, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h425, h427, h500, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h499, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h425, h426, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h536 | h536
              · linarith only [h425, h536, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
                · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                    · linarith only [h425, h540, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h542 | h542
                      · linarith only [h422, h536, h542, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h545 | h545
                          · rcases h0bigk with h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h0, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hc01, hlam, hphi, p546_1, u0ehi2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h420, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h420, h536, h539, hc12, hlam, hphi, ht01, p546_1, u0ehi2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hc02, hlam, hphi, p546_1, u0ehi0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, p546_1, u0ehi2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h0, h420, hc12, hlam, hphi, ht01, p546_1, u0ehi0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h0, h536, hc12, hlam, hphi, ht01, p546_1, u0ehi2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hc03, hlam, hphi, p546_1, u0ehi0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h422, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h425, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h536, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hc04, hlam, hphi, p546_1, u0ehi0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h423, hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h425, hc34, hlam, hphi, p546_1, u3ehi0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h425, hc34, hlam, hphi, ht01, ht12, ht23, p546_1, u0ehi4]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hc05, hlam, hphi, p546_1, u0ehi0]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h424, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hc05, hlam, hphi, p546_1, u0ehi2]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [h538, hlam, p546_1]
                            · have p546_0 := h546c.1
                              have p546_1 := h546c.2.1
                              have p546_2 := h546c.2.2.1
                              have p546_3 := h546c.2.2.2
                              linarith only [hlam, p546_0]
                          · linarith only [h425, h544, h545, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                        · linarith only [h425, h538, h540, h544, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h0, h539, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
                    · linarith only [h422, h425, h576, hc02, hlam, hphi, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h578 | h578
                      · linarith only [h422, h425, h578, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
                        · linarith only [h423, h538, h580, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                          · linarith only [h425, h538, h582, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h425, h582, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h0, h575, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h586 | h586
            · rcases m.htr 0 3 5 (by decide) (by decide) with h587 | h587
              · linarith only [h422, h424, h587, hlam]
              · linarith only [h586, h587, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h590 | h590
              · linarith only [h586, h590, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h592 | h592
                · linarith only [h423, h424, h592, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                    · linarith only [h422, h424, h595, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h597 | h597
                      · linarith only [h423, h424, h590, h595, h597, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h423, h424, h595, h597, hc35, hlam, hphi, u3ehi2]
                  · linarith only [h423, h424, h594, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h601 | h601
          · rcases m.htr 0 3 4 (by decide) (by decide) with h602 | h602
            · linarith only [h422, h423, h602, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h604 | h604
              · linarith only [h602, h604, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h606 | h606
                · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
                  · linarith only [h423, h607, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h607, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h422, h423, h606, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h611 | h611
            · linarith only [h422, h423, h611, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h613 | h613
              · linarith only [h611, h613, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h615 | h615
                · rcases m.htr 1 2 4 (by decide) (by decide) with h616 | h616
                  · linarith only [h423, h616, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h616, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h422, h423, h615, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h620 | h620
        · rcases m.htr 0 2 5 (by decide) (by decide) with h621 | h621
          · rcases m.htr 0 3 4 (by decide) (by decide) with h622 | h622
            · rcases m.htr 0 3 5 (by decide) (by decide) with h623 | h623
              · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
                · rcases m.htr 1 2 4 (by decide) (by decide) with h625 | h625
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h626 | h626
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h627 | h627
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h628 | h628
                        · linarith only [h422, h620, h628, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h422, h620, h624, h626, h628, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h422, h627, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h422, h620, h626, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h625, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h634 | h634
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h637 | h637
                        · linarith only [h620, h624, h637, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h639 | h639
                          · linarith only [h420, h422, h621, h624, h635, h637, h639, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                          · rcases h0bigk with h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c | h641c
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h0, hlam, p641_1]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, h624, hc45, hlam, hphi, ht34, p641_1, u3ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, hlam, p641_1]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, h624, hlam, p641_1]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h422, hc23, hlam, hphi, ht01, ht12, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h422, hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, h422, hc23, hlam, hphi, ht01, ht12, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, h422, h624, hc23, hlam, hphi, ht01, ht12, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hc03, hlam, hphi, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h621, h637, hc03, hlam, hphi, ht0b, ht45, ht5b, p641_1, u4ehi2]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, h422, hc23, hlam, hphi, ht01, ht12, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h420, h422, h624, hc23, hlam, hphi, ht01, ht12, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hc04, hlam, hphi, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h620, hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h622, hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h624, hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h621, hc02, hlam, hphi, p641_1, u0ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h621, hlam, p641_1]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h623, hlam, p641_0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [h422, h621, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p641_1, u4ehi0]
                            · have p641_0 := h641c.1
                              have p641_1 := h641c.2.1
                              have p641_2 := h641c.2.2.1
                              have p641_3 := h641c.2.2.2
                              linarith only [hlam, p641_0]
                      · linarith only [h422, h636, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h422, h620, h635, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h634, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h622, h623, hc35, hlam, hphi, u3ehi3]
            · linarith only [h422, h620, h622, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h672 | h672
            · rcases m.htr 0 3 5 (by decide) (by decide) with h673 | h673
              · rcases m.htr 0 4 5 (by decide) (by decide) with h674 | h674
                · linarith only [h620, h621, h674, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h679 | h679
                        · linarith only [h674, h679, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                        · linarith only [h620, h621, h677, h679, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h422, h673, h678, hlam]
                    · linarith only [h422, h673, h677, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h620, h621, h676, hc12, hc25, hlam, hphi]
              · linarith only [h672, h673, hc35, hlam, hphi, u3ehi3]
            · linarith only [h422, h620, h672, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h687 | h687
          · rcases m.htr 0 3 4 (by decide) (by decide) with h688 | h688
            · rcases m.htr 0 3 5 (by decide) (by decide) with h689 | h689
              · rcases m.htr 0 4 5 (by decide) (by decide) with h690 | h690
                · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                  · linarith only [h620, h691, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h691, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h620, h687, h690, hlam]
              · linarith only [h688, h689, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h696 | h696
              · linarith only [h688, h696, hc34, hlam, hphi, u3ehi4]
              · linarith only [h422, h687, h696, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h699 | h699
            · rcases m.htr 0 3 5 (by decide) (by decide) with h700 | h700
              · rcases m.htr 0 4 5 (by decide) (by decide) with h701 | h701
                · rcases m.htr 1 2 4 (by decide) (by decide) with h702 | h702
                  · linarith only [h620, h702, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h702, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                  · linarith only [h0, h620, h705, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h705, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h699, h700, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h709 | h709
              · linarith only [h699, h709, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h711 | h711
                · rcases m.htr 1 2 4 (by decide) (by decide) with h712 | h712
                  · linarith only [h0, h620, h712, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h712, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
                  · linarith only [h0, h620, h715, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h715, hc24, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
